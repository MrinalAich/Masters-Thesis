# Author  : Mrinal Aich
# Mail-id : cs16mtech11009@iith.ac.in, mr.mrinal.aich@gmail.com

from ryu.base import app_manager
from ryu.controller import ofp_event
from operator import attrgetter
from ryu.controller.handler import CONFIG_DISPATCHER, MAIN_DISPATCHER
from ryu.controller.handler import set_ev_cls
from ryu.ofproto import ofproto_v1_3
from ryu.lib.packet import packet
from ryu.lib.packet import ethernet, ether_types
from ryu.lib.packet import ether_types
from ryu.topology.api import get_switch, get_link, get_host, get_all_switch

from ryu.controller import mac_to_port
from ryu.topology import event, switches
from collections import defaultdict
from collections import deque
from sets import Set

import socket, select
from threading import Thread, Lock
from ryu.lib import hub
import Queue

from inspect import currentframe
import pdb, time, random, json, copy

from matplotlib import pyplot as plt
from matplotlib import animation
from ryu.ofproto import ether
from ryu.lib.packet import arp, packet

from ryu.lib.packet import ipv4, icmp, tcp,arp
from ryu.ofproto import ether
from ryu.ofproto import inet
from collections import namedtuple

#### GLOBAL MACROS

# Socket-level Constants
RECV_BUFFER = 4096
OPERATOR_API_SOCK_PORT = 12345
IP_ADDR = "0.0.0.0"
CPU_STATS_SERVER_PORT = 4444

UNIT_OF_BANDWIDTH = 1000 * 1000 # Mega

# Normalization Constants
alpha = 0.85
beta  = 0.0
gamma = 0.15

# Output Filenames
THROUGHPUT_ANIM_FILENAME = "throughput.json"
LATENCY_ANIM_FILENAME    = "latency.json"
CPU_ANIM_FILENAME        = "cpu.json"

LINK_LATENCY_ETH_TYPE   = 0x07c3
SWITCH_LATENCY_ETH_TYPE = 0x07c4

# TODO Hypervisor CPU Memory # In MB
ALL_HYPERVISOR_CPU_MEMORY_INIT = 100

LINK_BW_LIMIT = 10000 # 100 Kbps
LINK_BW_THRESHOLD = 0.98

# Timeout till the SLA agrrement starts coming
SLA_INPUT_TIMEOUT = 12

# Total VNFs installed
gUsedVNFIds   = {}
gUsedVNFCount = 0

# Docker SubNet
DOCKER_SUB_NET      = "192.168.111."
DOCKER_SUBNET_NAME  = 'overnet'

# Configuration File
SLA_CONFIG_FILE               = "sla_input.txt"
HYPERVISOR_CONFIGURATION_FILE = "hyp_config.txt"

# Miscellaneous 
SUCCESS = 1
FAILURE = 0

LOGGING_DEBUG = False
LOGGING_INFO  = 0

COLOR_WHITE = 0
COLOR_BLACK = 1

#### GLOBAL VARIABLES

# Prioirty Level
START_PRIORITY_VAL = 65500

# Cloud DPID
CLOUD_DPID = 5

# Hack for Bottleneck Detection
gNodeBottleneckHackCount = True

#### Structure of a SLA aggrement
class struct_SLA(object):
     def __init__(self, identifier, vnfInputList, vnfCPUMemReq, delayTolerated, reqBW, endUsersMac, endPointsDpid):
        self.identifier         = identifier
        self.isInstalled        = False          # Whether SLA is installed
        self.vnfInputList       = vnfInputList   # VNF Types
        self.vnfCPUMemReq       = vnfCPUMemReq   # CPU Mem required by VNF
        self.delayTolerated     = delayTolerated # ms
        self.reqBW              = reqBW          # Mbps
        self.endUsersMac        = endUsersMac    # End-Users
        self.endPointsDpid      = endPointsDpid  # End-Points DPID
        self.delayBuffer        = -1             # Delay-buffer
        self.compPathOfSLA      = {}             # Complete Path of SLA
        self.VNFsNetworkMac     = []
        self.VNFsNetworkDpid    = []
        self.VNFIds             = []
        self.centre             = -1
        self.pathToCentre       = {}
        self.pathOfServiceChain = []             # Used during Placement only
        self.vlanCommonTag      = ""

#### Structure of an installed VNF
class struct_Installed_VNF(object):
    def __init__(self, iden, slaIdentifier, vnfType, ipAddr, macAddr, memReq, hypervisor_dpid, servChainIndex):
        self.identifier         = iden
        self.slaIdentifier      = slaIdentifier    # SLA to which it belongs
        self.ipAddr             = ipAddr           # IP Address
        self.macAddr            = macAddr          # MAC Address
        self.vnfType            = vnfType          # Type of VNF
        self.cpuMemReq          = memReq           # CPU Mem Requirement
        self.dpid               = hypervisor_dpid  # Hypervisor's dpid
        self.servChainIndex     = servChainIndex   # Index in Service Chain

class Orchestrator(app_manager.RyuApp):
    OFP_VERSIONS = [ofproto_v1_3.OFP_VERSION]

    def __init__(self, *args, **kwargs):
        super(Orchestrator, self).__init__(*args, **kwargs)

        global gUsedVNFIds

        # Monitor
        self.DM_createMonitorThreads()

        self.mac_to_port = {}

        # Orchestrator
        self.orchestratorMsgQueue = ""
        self.DO_createOrchestratorThread()

        # API
        self.DAPI_adminThread()

        # Graph data structure
        self.m_graph = {}
        self.m_graph.setdefault('edges', {})
        self.m_graph.setdefault('switches', set())
        self.m_graph.setdefault('hosts', {})    # Hosts connected to the Switch
        
        # Monitor
        self.m_switchFlowStats        = {}
        self.m_switchLatencyStats     = {}
        self.m_linkLatencyStats       = {}
        self.m_hypervisorMemStats     = {}
        self.m_hypervisorCpuUtilStats = {}

        self.m_spTreeLinks = {}

        self.m_mac_to_dpid_port = {}
        self.m_dpid_to_mac_port = {}

        self.m_vnfOperationsOnStart      = {}
        self.m_SLACloudOperationsOnStart = {}

        # Hypervisor VNF status
        self.m_hypVNFStatus     = {}

        self.m_topology_api_app = self

        self.debugFlag = False
        
        self.m_SLAsCount = 0
        self.m_SLAs = {} # Maintains all the SLAs

        self.m_end_users_to_SLA = {} # Reverse Map
        self.m_ovs_mac          = {} # Hardcoded MAC address for OVS based on dpid 

        # Communication with the Hypervisor System
        self.m_server_socket          = ""
        self.m_dpid_to_hyp_ip         = self.read_HYP_config_file() # Map of dpid to IP Address of Hypervisor
        self.m_hypervisor_socket_list = []
        self.m_hyp_ip_sockfd_pair     = []                     # Map Hypervisor IP to sockfds
        self.m_socket_mutex           = Lock()                 # TODO :Mutex lock for Socket DS's

        # Init unused VNF Ids
        for index in range(1, 255):
            gUsedVNFIds[index] = False

    # Monitor Thread
    def _monitorLink_SwitchStatsThread(self):

        while True:
            # Flow Stats from Switch
            for dp in self.m_graph['switches']:
                self.DM_request_stats(dp)

            hub.sleep(1)

            # Switch Latency
            for dpid in self.m_graph['switches']:

                datapath   = self.getDatapath(dpid.id)

                # Temporary Mac addresses, Dst Mac Address contains identifier
                switchFlowStatsSrcMac = datapath.ports[datapath.ofproto.OFPP_LOCAL].hw_addr
                switchFlowStatsDstMac = "00:00:00:00:" + format(dpid.id,'x') + str(':') + format(dpid.id,'x')
            
                self.sendPacket(SWITCH_LATENCY_ETH_TYPE, dpid.id, datapath.ofproto.OFPP_CONTROLLER, switchFlowStatsSrcMac, switchFlowStatsDstMac, dpid, 0)

            #pdb.set_trace()
            # Link Latency
            for dpid in self.m_graph['edges']:

                # Retrieve Nbrs of the current Dpid
                for nbr_dpid,out_port in self.m_graph['edges'][dpid].items():

                    # Initialize Link monitoring
                    if dpid > nbr_dpid:

                        if dpid not in self.m_linkLatencyStats:
                            self.m_linkLatencyStats[dpid] = {}
                        
                        if nbr_dpid not in self.m_linkLatencyStats[dpid]:
                            self.m_linkLatencyStats[dpid][nbr_dpid] = {}
                            self.m_linkLatencyStats[dpid][nbr_dpid]['lastSentTime']   = float(0.0)
                            self.m_linkLatencyStats[dpid][nbr_dpid]['lastUpdateTime'] = float(0.0)
                            self.m_linkLatencyStats[dpid][nbr_dpid]['data']           = float(0.0)
                
                        datapath = self.getDatapath(dpid)

                        # format(number , 'x') converts number to hex removing 'x' here switch number to hex 
                        linkFlowStatsDstMac = "00:00:00:11:" + format(dpid,'x') + str(':') + format(nbr_dpid,'x')
                        linkFlowStatsSrcMac = datapath.ports[datapath.ofproto.OFPP_LOCAL].hw_addr

                        self.sendPacket(LINK_LATENCY_ETH_TYPE, dpid, out_port, linkFlowStatsSrcMac, linkFlowStatsDstMac, dpid, nbr_dpid)

            hub.sleep(1)

    # Function sends custom packet for Link monitoring
    # Ref: Monitoring Latency with Openflow 
    def sendPacket(self, eth_type, current_dpid, out_port, temp_src_mac, temp_dst_mac, src_dpid, dst_dpid):
    
        # Create a custom packet
        ethernet_type   = eth_type
        ethernet_header = ethernet.ethernet(ethertype=ethernet_type, src=temp_src_mac, dst=temp_dst_mac)
        ip_header       = ipv4.ipv4(total_length=len(ipv4.ipv4()), proto=inet.IPPROTO_ICMP, ttl=1, src='192.111.111.111', dst='192.222.222.222')

        custom_packet = packet.Packet()
        custom_packet.add_protocol(ethernet_header)
        custom_packet.add_protocol(ip_header)
        custom_packet.serialize()

        datapath = self.getDatapath(current_dpid)
        actions  = [datapath.ofproto_parser.OFPActionOutput(port=out_port)]

        msg = datapath.ofproto_parser.OFPPacketOut(datapath=datapath, buffer_id=0xffffffff, in_port=datapath.ofproto.OFPP_CONTROLLER, actions=actions, data=custom_packet.data)
       
        currentTime = time.time() * 1000 # In Milliseconds

        # Maintain Timestamp
        if eth_type == SWITCH_LATENCY_ETH_TYPE:
            # Initialize, used for Graphs
            if 'startTime' not in self.m_switchLatencyStats[current_dpid]:
                self.m_switchLatencyStats[current_dpid]['startTime'] = currentTime

            self.m_switchLatencyStats[current_dpid]['lastSentTime'] = currentTime

        elif eth_type == LINK_LATENCY_ETH_TYPE:
            # Initialize, used for Graphs
            if 'startTime' not in self.m_linkLatencyStats[src_dpid][dst_dpid]:
                self.m_linkLatencyStats[src_dpid][dst_dpid]['startTime'] = currentTime

            self.m_linkLatencyStats[src_dpid][dst_dpid]['lastSentTime']  = currentTime

        datapath.send_msg(msg)

    # Orchestrator Thread
    def _orchestratorThread(self):
        self.orchestratorMsgQueue = Queue.Queue()

        # Socket server create
        self.DO_openSocketThreadAPI()

        while(1):

            # Check Message Queue
            self.DO_checkMessageQueue()
            hub.sleep(0.1)

    # ------------------------------------------------------------------------------
    # Utility Functions
    # ------------------------------------------------------------------------------
    # Creates the Orchestrator Thread
    def DO_createOrchestratorThread(self):
        try:
            # Create the Orchestrator Thread
            self.socket_thread = hub.spawn(self._orchestratorThread)
        except:
            LOG_DEBUG("Error: unable to start Orchestrator thread")

    # Check for messages in Message Queue
    def DO_checkMessageQueue(self):

        if not self.orchestratorMsgQueue.empty():

            message = self.orchestratorMsgQueue.get()
            if message['type'] == "FlowManager":
                self._DO_handleFlowManagerMessage(message)


            elif message['type'] == "Operator":
                self._DO_handleOperatorMessage(message['message'], message['socket'])


            elif message['type'] == "Detector":
                self._DO_handleDetectorMessage(message)

    # -------------------------------------------------------------------------------------------------------------------------
    #    ADMIN API MODULE : Temporary TODO To be removed.
    # -------------------------------------------------------------------------------------------------------------------------

    # Creates the Admin Thread for periodic SLA input
    def DAPI_adminThread(self):
        self.DAPI_slaInputThread = hub.spawn(self._slaInputThread)

    # SLA Input Thread
    def _slaInputThread(self):

        hub.sleep(SLA_INPUT_TIMEOUT)

        # Reads SLAs to be installed
        if False:
            self.readSLAList()

            for key,slaObject in self.m_SLAs.items():
                # Creates reverse Map of EndPoints to SLAs
                self.mapEndUsersToSLAs(slaObject)

                # Algorithm - 1 : Placement of the SLA
                self.placementOfSLA(slaObject)
                
        else:
            # Hardcoded SLA agreement
            # Format   = struct_SLA(# ID, [<List of VNFs>],        [CPU], DelayTolerated, reqBandwidth, endUsersMacAddr, endUsersConnDpid)
            
            #slaObject = struct_SLA(self.m_SLAsCount, ['Middlebox'], [10], 10, 100, ['00:00:00:00:00:11', '00:00:00:00:00:21'], [1,2])
            #slaObject = struct_SLA(self.m_SLAsCount, ['Middlebox'], [10], 10, 100, ['00:00:00:00:00:21', '00:00:00:00:00:31'], [2,3])
            
            slaObject  = struct_SLA(self.m_SLAsCount, ['Middlebox'], [10], 10, 100, ['00:00:00:00:00:11', '00:00:00:00:00:31'], [1,3])
            
            slaObject  = struct_SLA(self.m_SLAsCount, ['Middlebox'], [10], 10, 100, ['00:00:00:00:00:11', '00:00:00:00:00:41'], [1,4])
            slaObject  = struct_SLA(self.m_SLAsCount, ['Middlebox', 'Middlebox'], [10, 10], 10, 100, ['00:00:00:00:00:11', '00:00:00:00:00:32'], [1,3])
            slaObject  = struct_SLA(self.m_SLAsCount, ['Middlebox'], [10], 10, 100, ['00:00:00:00:00:11', '00:00:00:00:00:31'], [1,3])
            
            # SLACase
            slaObject  = struct_SLA(self.m_SLAsCount, ['Middlebox'], [10], 10, 100, ['00:00:00:00:00:11', '00:00:00:00:00:32'], [1,3])
            slaObject  = struct_SLA(self.m_SLAsCount, ['Middlebox', 'Middlebox'], [10, 10], 10, 100, ['00:00:00:00:00:11', '00:00:00:00:00:31'], [1,3])
            slaObject  = struct_SLA(self.m_SLAsCount, ['Middlebox'], [10], 10, 100, ['00:00:00:00:00:11', '00:00:00:00:00:31'], [1,3])
            slaObject  = struct_SLA(self.m_SLAsCount, ['Middlebox', 'Middlebox'], [10, 10], 10, 100, ['00:00:00:00:00:11', '00:00:00:00:00:42'], [1,4])
            slaObject  = struct_SLA(self.m_SLAsCount, ['Middlebox', 'Middlebox', 'Middlebox'], [10, 10, 10], 10, 100, ['00:00:00:00:00:11', '00:00:00:00:00:21'], [1,2])
            slaObject  = struct_SLA(self.m_SLAsCount, ['Middlebox'], [10], 10, 100, ['00:00:00:00:00:11', '00:00:00:00:00:31'], [1,3])
            slaObject  = struct_SLA(self.m_SLAsCount, ['Middlebox', 'Middlebox'], [10, 10], 10, 100, ['00:00:00:00:00:11', '00:00:00:00:00:21'], [1,2])
            slaObject  = struct_SLA(self.m_SLAsCount, ['Middlebox', 'Middlebox'], [10, 10], 10, 100, ['00:00:00:00:00:11', '00:00:00:00:00:41'], [1,4])

            self.m_SLAs[slaObject.identifier] = slaObject

    # Reads SLAs to be installed over the network
    def readSLAList(self):
        pdb.set_trace()
        
        skipFirstLine = True
        chars_to_remove = ['[', ']', '\'']
        temp_chars_to_remove = ['[', ']']

        with open(SLA_CONFIG_FILE,'rb') as file:
            for line in file:

                # Skip First Line, contains Format
                if skipFirstLine:
                    skipFirstLine = False
                    line.rstrip()
                    continue
               
                # Empty Line, interpret as EOF
                elif line == "\n" or line == "\r\n" or line == "\r":
                    return

                data = line.rstrip()
                data = data.split(',')

                # VNFTypes
                vnfTypes = data[0].strip(' ')
                vnfTypes = vnfTypes.translate(None, ''.join(chars_to_remove)).split(' ')

                # CPU Mem requiremtn of VNFs
                vnfsMemReq = data[1].strip(' ')
                vnfsMemReq = vnfsMemReq.translate(None, ''.join(temp_chars_to_remove)).split(' ')
                for index in range(0, len(vnfsMemReq)):
                    vnfsMemReq[index] = int(vnfsMemReq[index])

                # Delay Tolerated
                delayTolerated = int(data[2].strip(' '))

                # Minimum Bandwidth Required
                reqBW = int(data[3].strip(' '))

                # Retreive Hosts MAC Addresses
                macAddrs = data[4].strip(' ')
                macAddrs = macAddrs.translate(None, ''.join(chars_to_remove)).split(' ')

                # Retreieve Hosts Dpid
                dpids    = data[5].strip(' ')
                dpids    = dpids.translate(None, ''.join(chars_to_remove)).split(' ')
                for index in range(0, len(dpids)):
                    dpids[index] = int(dpids[index])

                if len(macAddrs) != len(dpids):
                    print "Error: Incorrect SLA, Count of MAC Addr and their Dpids do not match. Ignoring the SLA..."
                    continue

                self.m_SLAsCount = self.m_SLAsCount + 1

                slaObject = struct_SLA(self.m_SLAsCount, vnfTypes, vnfsMemReq, delayTolerated, reqBW, macAddrs, dpids)
                self.m_SLAs[self.m_SLAsCount] = slaObject



    # -------------------------------------------------------------------------------------------------------------------------
    #    MONITORING MODULE : 
    #    Reference simple_monitor13.py
    # -------------------------------------------------------------------------------------------------------------------------

    # Creates the Monitor Thread
    def DM_createMonitorThreads(self):
        self.DM_monitor_thread          = hub.spawn(self._monitorLink_SwitchStatsThread)
        self.DM_cpu_stats_server_thread = hub.spawn(self._cpuStatsServerThread)
       
    # Creates Server Thread to receive all CPU Statistics from the Hypervisors
    def _cpuStatsServerThread(self):

        # Socket-level functions
        self.m_server_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.m_server_socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.m_server_socket.bind((IP_ADDR, CPU_STATS_SERVER_PORT))
        self.m_server_socket.listen(10)
     
        # Add server socket object to the list of readable connections
        self.m_hypervisor_socket_list.append(self.m_server_socket)
        while 1:
            # get the list sockets which are ready to be read through select
            # 4th arg, time_out  = 0 : poll and never block
            ready_to_read,ready_to_write,in_error = select.select(self.m_hypervisor_socket_list,[],[],0)
          
            for sock in ready_to_read:
                # new connection request recieved
                if sock == self.m_server_socket: 
                    sockfd,addr= self.m_server_socket.accept()
                    self.m_hypervisor_socket_list.append(sockfd)
                    self.m_hyp_ip_sockfd_pair.append(make_tuple(addr, sockfd))

                # message from a Hypervisor system, not a new connection
                else:
                    try:
                        data = sock.recv(RECV_BUFFER)
                        if data:
                            # Function interprets the Docker stats information from a Hypervisor
                            self.processHypervisorCPUInfo(data)

                        else:
                            LOG_DEBUG("Received empty data from Hypervisor. Closing Socket connection" % pair.val2)

                            # Remove the socket that's broken
                            if sock in self.m_hypervisor_socket_list:
                                self.m_hypervisor_socket_list.remove(sock)

                            # Clean up related data-structures
                            for pair in self.m_hyp_ip_sockfd_pair:
                                if pair.val2 == sock:
                                    self.m_hyp_ip_sockfd_pair.remove(pair)
                                    break
                    # exception 
                    except:
                        continue

        self.m_server_socket.close()

    # Updates Hypervisor's CPU Utilization by Docker Containers
    def processHypervisorCPUInfo(self, data):
        global gNodeBottleneckHackCount

        data = data.split(":")
        hypervisorIP       = str(data[0])
        hypervisorRcvdTime = float(data[1])
        percentCpuUsage    = float(data[2])
        dpid               = ""
        
        for hDpid,ipAddr in self.m_dpid_to_hyp_ip.items():
            if ipAddr == hypervisorIP:
                dpid = hDpid
                break

        # Sanity Check
        if dpid == "":
            LOG_ERROR("Hypervisor IP (%s) to Dpid map not found. This scenario should not occur. Programming Error!!!" % (hypervisorIP))
            return

        # TODO: Bottleneck Detection Module
        # Tweak
        if False and dpid == 2:
            gNodeBottleneckHackCount += 1
            if gNodeBottleneckHackCount == 10:
                LOG_DEBUG("CPU Utilization Bottleneck detected at Hypervisor(%s). Neccessary actions to be taken." % hypervisorIP)

                # Handle Node Bottleneck
                self.handleNodeBottleneck(dpid)

        if self.debugFlag:
            print "Hypervisor [%s] at %s | %s" % (hypervisorIP, hypervisorRcvdTime, percentCpuUsage)

        if dpid not in self.m_hypervisorCpuUtilStats:
            return

        # 1st time information from the Hypervisor
        if self.m_hypervisorCpuUtilStats[dpid]['startRcvdTime'] == float(0.0):
            self.m_hypervisorCpuUtilStats[dpid]['startRcvdTime'] = hypervisorRcvdTime

        self.m_hypervisorCpuUtilStats[dpid]['data']         = percentCpuUsage
        self.m_hypervisorCpuUtilStats[dpid]['lastRcvdTime'] = hypervisorRcvdTime

        if self.debugFlag:
            LOG_DEBUG("CPU Stat Update of %s @ %s -> %s" % (hypervisorIP,
                       str(self.m_hypervisorCpuUtilStats[dpid]['lastRcvdTime']),
                       str(self.m_hypervisorCpuUtilStats[dpid]['data'])))

        self.write_to_file(CPU_ANIM_FILENAME, self.m_hypervisorCpuUtilStats)

    # Function requests Port Stats from Switches
    def DM_request_stats(self, datapath):
        currentTime = float('%.2f' % time.time())

        ofproto = datapath.ofproto
        parser  = datapath.ofproto_parser
        dpid    = datapath.id

        if dpid not in self.m_switchFlowStats:
            self.m_switchFlowStats[dpid] = {}

        # Maintaing Stats Request time
        self.m_switchFlowStats[dpid]['LastSentTime'] = currentTime
        req = parser.OFPPortStatsRequest(datapath, 0, ofproto.OFPP_ANY)
        datapath.send_msg(req)

    # Event - OFP Flow Stats Reply
    @set_ev_cls(ofp_event.EventOFPFlowStatsReply, MAIN_DISPATCHER)
    def _flow_stats_reply_handler(self, ev):
        body = ev.msg.body

        self.logger.info('datapath         '
                         'in-port  eth-dst           '
                         'out-port packets  bytes')
        self.logger.info('---------------- '
                         '-------- ----------------- '
                         '-------- -------- --------')
        for stat in sorted([flow for flow in body if flow.priority == 1], 
                            key=lambda flow: (flow.match['in_port'], flow.match['eth_dst'])):
            self.logger.info('%016x %8x %17s %8x %8d %8d',
                             ev.msg.datapath.id,
                             stat.match['in_port'], stat.match['eth_dst'],
                             stat.instructions[0].actions[0].port,
                             stat.packet_count, stat.byte_count)

    # Event - OFP Port Stats Reply
    @set_ev_cls(ofp_event.EventOFPPortStatsReply, MAIN_DISPATCHER)
    def _port_stats_reply_handler(self, ev):
        body = ev.msg.body

        for stat in sorted(body, key=attrgetter('port_no')):
            if stat.port_no != 0xfffffffe: # Ignoring Local Port
                self.DM_update_bandwidth(ev.msg.datapath.id, stat.port_no, stat.rx_bytes, stat.tx_bytes)

        if LOGGING_DEBUG:
            self.logger.info('datapath         port     rx-pkts  rx-bytes rx-error tx-pkts  tx-bytes tx-error')
            self.logger.info('---------------- -------- -------- -------- -------- -------- -------- --------')
            for stat in sorted(body, key=attrgetter('port_no')):
                self.logger.info('%016x %8x %8d %8d %8d %8d %8d %8d',ev.msg.datapath.id, stat.port_no,
                                    stat.rx_packets, stat.rx_bytes, stat.rx_errors, stat.tx_packets, stat.tx_bytes, stat.tx_errors)

    # Functions updates all-Ports Bandwidth acheived
    def DM_update_bandwidth(self, dpid, port, rxBytes, txBytes):

        # Sanity Checks
        if dpid not in self.m_switchFlowStats:
            self.m_switchFlowStats[dpid] = {}
            LOG_ERROR("This scenario should not occur. Programming Error!!!")

        # Initialize Port-Stats Monitoring
        if port not in self.m_switchFlowStats[dpid]:
            currentTime = float('%.2f' % time.time())
            self.m_switchFlowStats[dpid][port] = {}
            self.m_switchFlowStats[dpid][port]['startRecordedTime'] = currentTime
            self.m_switchFlowStats[dpid][port]['LastTotalBytes']    = rxBytes + txBytes
            self.m_switchFlowStats[dpid][port]['LastRecordedTime']  = currentTime
            self.m_switchFlowStats[dpid][port]['data'] = []

        else:
            # Update Port-Stats Monitoring
            currentTime = float('%.2f' % time.time())
            currentBytesProcessed = rxBytes + txBytes

            deltaBytesProcessed = abs(currentBytesProcessed - self.m_switchFlowStats[dpid][port]['LastTotalBytes'])
            deltaTime   = currentTime - self.m_switchFlowStats[dpid][port]['LastRecordedTime']
            
            durationFromStart = currentTime - self.m_switchFlowStats[dpid][port]['startRecordedTime']
            
            # Sanity Check
            if deltaTime == float(0.0):
                LOG_ERROR("This scenario should not occur. Programming or System Error!!!")
                return

            bandwidthAcheived = float(deltaBytesProcessed * 8)/float(float(UNIT_OF_BANDWIDTH) * float(deltaTime)) # Kbps
            self.m_switchFlowStats[dpid][port]['data'] = [durationFromStart, bandwidthAcheived]

            self.m_switchFlowStats[dpid][port]['LastTotalBytes']   = currentBytesProcessed
            self.m_switchFlowStats[dpid][port]['LastRecordedTime'] = currentTime

            self.write_to_file(THROUGHPUT_ANIM_FILENAME, self.m_switchFlowStats)

    # Functions updates Link Latency
    def DM_update_latency(self, dpid, ethernet_type, eth):

        curr_time = float('%.2f' % (time.time() * 1000)) # In Milliseconds

        src_mac = eth.src
        dst_mac = eth.dst

        # Sanity Check
        if "00:00:00" not in dst_mac:
            return

        ### Switch Latency
        if ethernet_type == SWITCH_LATENCY_ETH_TYPE:

            # Format of Dst_mac : "00:00:00:00:(dpid):(dpid)"
            dpid = int(dst_mac.split(":")[4].lstrip())

            # Sanity Check
            if dpid not in self.m_switchLatencyStats or 'lastSentTime' not in self.m_switchLatencyStats[dpid]:
                LOG_ERROR("This scenario should not occur. Programming Error!!!")
                return

            # Update Switch-Latency Monitoring
            sent_time = self.m_switchLatencyStats[dpid]['lastSentTime']
            deltaSwitchLatencyTime = curr_time - sent_time
            self.m_switchLatencyStats[dpid]['data']           = float(deltaSwitchLatencyTime/2)
            self.m_switchLatencyStats[dpid]['lastUpdateTime'] = float(curr_time)

        ### Link Latency
        elif ethernet_type == LINK_LATENCY_ETH_TYPE:

            # Format of Dst_mac : "00:00:00:00:(dpid):(nbr_dpid)"
            dpid1 = int(dst_mac.split(":")[4].lstrip())
            dpid2 = int(dst_mac.split(":")[5].lstrip())
            
            # Sanity Check
            if dpid1 not in self.m_linkLatencyStats or dpid2 not in self.m_linkLatencyStats[dpid1] or 'startTime' not in self.m_linkLatencyStats[dpid1][dpid2]:
                LOG_ERROR("This scenario should not occur. Programming Error!!!")
                if self.debugFlag:
                    LOG_DEBUG("Link Latency Packet: Src Dpid (%s) -> Dst Dpid (%s)" % (dpid1, dpid2))
                return

            # Check, required for Triangular Rule Calculation
            if dpid1 not in self.m_switchLatencyStats or dpid2 not in self.m_switchLatencyStats:
                LOG_DEBUG("Switch Latency Module not initialized. Programming Error!!!")
                return

            # Calculate Latency since the last sent
            deltaLinkLatency = curr_time - self.m_linkLatencyStats[dpid1][dpid2]['lastSentTime']

            dpid1_latency = self.m_switchLatencyStats[dpid1]['data']
            dpid2_latency = self.m_switchLatencyStats[dpid2]['data']
            link_latency  = deltaLinkLatency - dpid1_latency - dpid2_latency

            # Update Link Latency
            self.m_linkLatencyStats[dpid1][dpid2]['data']           = abs(link_latency)
            self.m_linkLatencyStats[dpid1][dpid2]['lastUpdateTime'] = curr_time

            if False:
                LOG_DEBUG("Switch Latency : %s -        %s seconds" % (dpid1, dpid1_latency))
                LOG_DEBUG("Switch Latency : %s -        %s seconds" % (dpid2, dpid2_latency))
                LOG_DEBUG("Round  Latency : %s <-> %s : %s seconds" % (dpid1, dpid2, deltaLinkLatency))
                LOG_DEBUG("Latency over the link %s <---> %s :  %s seconds " % (dpid1, dpid2, abs(link_latency)))

            self.write_to_file(LATENCY_ANIM_FILENAME, self.m_linkLatencyStats)

    # Function writes data to a file
    def write_to_file(self, fileName, data):
        with open(fileName, mode='w') as outfile:
            json.dump(data, outfile)
        return

    # -------------------------------------------------------------------------------------------------------------------------
    #    FLOW MANAGER MODULE : AS RYU CONTROLLER APPLICATION - OPENFLOW v1.3
    # -------------------------------------------------------------------------------------------------------------------------
 
    @set_ev_cls(ofp_event.EventOFPSwitchFeatures, CONFIG_DISPATCHER)
    def switch_features_handler(self, ev):
        datapath = ev.msg.datapath
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser

        # install table-miss flow entry
        #
        # We specify NO BUFFER to max_len of the output action due to
        # OVS bug. At this moment, if we specify a lesser number, e.g.,
        # 128, OVS will send Packet-In with invalid buffer_id and
        # truncated packet data. In that case, we cannot output packets
        # correctly.  The bug has been fixed in OVS v2.1.0.
        match = parser.OFPMatch()
        actions = [parser.OFPActionOutput(ofproto.OFPP_CONTROLLER)]
        self.add_flow(datapath, 1, match, actions)

        match = parser.OFPMatch(eth_type=ether_types.ETH_TYPE_ARP)
        actions = [parser.OFPActionOutput(ofproto.OFPP_CONTROLLER)]
        self.add_flow(datapath, 65535, match, actions)

    # Adds Flow entry on the OVS connected with the datapath
    def add_flow(self, datapath, priority, match, actions, buffer_id=None):

        if int(priority) == 65502 or priority == "65502":
            pdb.set_trace()

        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser

        inst = [parser.OFPInstructionActions(ofproto.OFPIT_APPLY_ACTIONS, actions)]
        if buffer_id:
            mod = parser.OFPFlowMod(datapath=datapath, buffer_id=buffer_id,
                                    priority=priority, match=match,
                                    instructions=inst)
        else:
            mod = parser.OFPFlowMod(datapath=datapath, priority=priority,
                                    match=match, instructions=inst)
        datapath.send_msg(mod)

    # Deletes Flow entry on the OVS connected with the datapath
    def del_flow(self, datapath, priority, match):
        ofproto = datapath.ofproto
        parser  = datapath.ofproto_parser

        # OFPFC_DELETE_STRICT : Delete entry strictly matching wildcards and priority.
        mod     = parser.OFPFlowMod(datapath=datapath, priority=priority,
                                    match=match, command=ofproto.OFPFC_DELETE_STRICT,
                                    out_port=ofproto.OFPP_ANY,
                                    out_group=ofproto.OFPG_ANY)
        datapath.send_msg(mod)

    @set_ev_cls(ofp_event.EventOFPPacketIn, MAIN_DISPATCHER)
    def _packet_in_handler(self, ev):
        # If you hit this you might want to increase
        # the "miss_send_length" of your switch
        if ev.msg.msg_len < ev.msg.total_len:
            self.logger.debug("packet truncated: only %s of %s bytes",
                              ev.msg.msg_len, ev.msg.total_len)
        msg = ev.msg
        datapath = msg.datapath
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        in_port = msg.match['in_port']

        pkt = packet.Packet(msg.data)
        eth = pkt.get_protocols(ethernet.ethernet)[0]

        if self.debugFlag:
            print "Packet passing started"
            print "-------------------------------------------------------------------------------------------------------------------------------"
            self.debugFlag = False

        # Ignore LLDP and IPv6 packets 
        if eth.ethertype == ether_types.ETH_TYPE_LLDP or \
           eth.ethertype == ether_types.ETH_TYPE_IPV6: 
            return

        # Check for Link Monitoring Packets
        if eth.ethertype in [LINK_LATENCY_ETH_TYPE, SWITCH_LATENCY_ETH_TYPE]:

            # Handle Link Monitoring Packets
            self.DM_update_latency(datapath.id, eth.ethertype, eth)
            return

        dst_mac = eth.dst
        src_mac = eth.src
        dpid = datapath.id

        if "00:00:00:00:00" not in src_mac and "00:00:00:00:00" not in dst_mac:
            return

        match   = []
        actions = []

        src_dpid = dpid
        retVal,dst_dpid = self.get_dpid_from_mac(dst_mac)

        # Check whether EndPoints belong to an SLA
        isUsersBelongToSLA = self.checkEndUsersToSLA(src_mac, dst_mac)

        # Unknown Destination Host
        # Flood along the edge switches and the Hosts connected to the nodes of the spanning Tree
        if eth.ethertype == ether_types.ETH_TYPE_ARP or retVal != SUCCESS:

            sendPktOutFlag = False
            # Forwarding to the switches
            if dpid in self.m_graph['edges']:
                for nbr_dpid,out_port in self.m_graph['edges'][dpid].items():
                    if in_port != out_port and nbr_dpid in self.m_spTreeLinks and dpid in self.m_spTreeLinks[nbr_dpid]:
                        actions.append(datapath.ofproto_parser.OFPActionOutput(out_port))
                        sendPktOutFlag = True

                        if LOGGING_DEBUG:
                            LOG_DEBUG("%s | Switch: %s <-> Port : %s" % (dpid, nbr_dpid, out_port))

            # Forwarding to the hosts
            if dpid in self.m_graph['hosts']:
                for mac,out_port in self.m_graph['hosts'][dpid].items():
                    if out_port != in_port:
                        actions.append(datapath.ofproto_parser.OFPActionOutput(out_port))
                        sendPktOutFlag = True

                        if LOGGING_DEBUG:
                            LOG_DEBUG("%s | Host: %s  <-> Port : %s" % (dpid, mac, out_port))

            # Send the packet
            if sendPktOutFlag:
                data = None
                if msg.buffer_id == ofproto.OFP_NO_BUFFER:
                    data = msg.data
                out = datapath.ofproto_parser.OFPPacketOut( datapath=datapath, buffer_id=msg.buffer_id, in_port=in_port, actions=actions, data=data)
                datapath.send_msg(out)
        
        # First Packet of an SLA, installing respective flow rules
        elif len(isUsersBelongToSLA):

            # Retreive the IP packet
            ip_pkt = pkt.get_protocols(ipv4.ipv4)[0]
            sla_object = 0

            for sla_object in isUsersBelongToSLA:
                LOG_DEBUG("%s & %s belong to SLA : %s" % (src_mac, dst_mac, sla_object.identifier))
                LOG_ERROR("This scenario should not occur *** NOW ***. Programming Error!!!")
                break

            # TODO: Use only One function to handle First and Rest flow rule installs
            self.installSLAFlowRules(sla_object, src_mac, dst_mac, msg, ofproto, parser, in_port, ip_pkt.src, ip_pkt.dst, sla_object.compPathOfSLA[src_mac][dst_mac]['priority'])

            # Add New flow rules for this change with Higher Priority
            self.updateNewSLAFlowRules(sla_object, False, src_mac, dst_mac)

            # Remove Previous Flow Rules
            if sla_object.compPathOfSLA[src_mac][dst_mac]['prevPath'] != []:

                self.removeOldSLAFlowRules(sla_object, src_mac, dst_mac, sla_object.compPathOfSLA[src_mac][dst_mac]['prevPath'], [], [])
                sla_object.compPathOfSLA[src_mac][dst_mac]['prevPath'] = []

            LOG_DEBUG("Flow rules installed and Current Packet forwarded.")

        # Known Host - Install flow rules along the path
        else:
            LOG_DEBUG("Known Host - Install flow rules along the path")
            LOG_DEBUG("This Scenario should not occur!!!")

    # Assign VNF Resources
    def assignVNFResources(self, sla, index, dpid, isMigrated):
        global gUsedVNFIds, gUsedVNFCount

        gUsedVNFCount += 1

        # Find the VNF Id not in use
        for item, val in gUsedVNFIds.items():
            if gUsedVNFIds[item] == False and item >= 50: # TODO
                vnfId = item
                break

        ipAddr  = DOCKER_SUB_NET + str(vnfId)
        macAddr = "00:00:00:00:00:" + str(vnfId).zfill(2)

        # Update VNF MAC for the Migrated VNF
        if isMigrated:
            sla.VNFsNetworkMac[index] = macAddr
            sla.VNFIds[index]         = vnfId
        else:
            sla.VNFsNetworkMac.append(macAddr)
            sla.VNFIds.append(vnfId)

        vnfInfo = struct_Installed_VNF(vnfId, sla.identifier, sla.vnfInputList[index], ipAddr, macAddr, sla.vnfCPUMemReq[index], dpid, index)
        self.m_hypervisorMemStats[dpid]['used'] += sla.vnfCPUMemReq[index]

        gUsedVNFIds[vnfId] = vnfInfo

        return gUsedVNFIds[vnfId]

    # Removes assigned VNF Resouces 
    def recoverVNFResources(self, sla, vnfInfo):
        global gUsedVNFIds, gUsedVNFCount

        vnfId = vnfInfo.identifier
        dpid  = vnfInfo.dpid

        # Recover Hypervisor CPU Mem Utilization
        self.m_hypervisorMemStats[dpid]['used'] -= vnfInfo.cpuMemReq

        # VNF Id to be re-used
        gUsedVNFIds[vnfInfo.identifier] = False # Empty Slot
        gUsedVNFCount -= 1

        return

    # Creates message to Start VNF at Hypervisor
    def sendStartVNFCommand(self, vnfInfo, sockfd):
        container_type = vnfInfo.vnfType.lower()
        container_id   = vnfInfo.identifier
        cont_name      = "c%s" % (container_id)
        cont_mac       = vnfInfo.macAddr
        cont_ip        = vnfInfo.ipAddr

        msgs = []

        # Middlebox
        if container_type == "middlebox":
            cont_ip   = "192.168.111.%s" % (container_id)
            msgs.append("docker run -d --mac-address=\"%s\" --name %s --network=%s --ip=%s --privileged mrinalaich/middlebox:1.0 sleep 10000" % (cont_mac, cont_name, DOCKER_SUBNET_NAME, cont_ip))
            msgs.append("docker exec %s python repreater.py &" % (cont_name))

        # BusyBox
        elif container_type == "busy_box":
            cont_ip   = "192.168.111.%s" % (container_id)
            msgs.append("docker run -d --mac-address=\"%s\" --name %s --network=%s --ip=%s centos:latest sleep 10000" % (cont_mac, cont_name, DOCKER_SUBNET_NAME, cont_ip))

        else:
            LOG_DEBUG("Container %s not supported." % container_type)

        # Send Message to Hypervisor
        for msg in msgs:
            sockfd.send(msg)
            hub.sleep(0.2)

    # Creates message to Stop VNF at Hypervisor
    def sendStopVNFCommand(self, vnfInfo, sockfd):
        cont_name = "c%s" % (vnfInfo.identifier)

        # Force the removal of a running container (uses SIGKILL)
        msg = "docker rm --force %s" % cont_name

        # Send Message to Hypervisor
        sockfd.send(msg)
        hub.sleep(0.5)

    # Generate Forwarding Commands
    def generateForwardingCommand(self, cont_name, ipAddr1, ipAddr2):
        msgs = []
        msgs.append("docker exec %s iptables -t nat -A PREROUTING -d %s -j DNAT --to-destination %s" % (cont_name, ipAddr1, ipAddr2))
        msgs.append("docker exec %s iptables -t nat -A POSTROUTING -s %s -j SNAT --to-source %s" % (cont_name, ipAddr2, ipAddr1))

        return msgs

    # Creates message for Forwarding in VNFs
    def sendForwardingVNFCommand(self, sla, vnfInfo, sockfd, serviceChainIndex):

        container_type = vnfInfo.vnfType.lower()
        container_id   = vnfInfo.identifier
        cont_name      = "c%s" % (container_id)
        cont_mac       = vnfInfo.macAddr
        cont_ip        = vnfInfo.ipAddr

        '''
        # Retrieve all Host IPs
        hostIPs = []
        for host_mac in sla.endUsersMac:
            host_id = int(host_mac.split(":")[5])
            host_ip = DOCKER_SUB_NET + str(host_id)
            hostIPs.append(host_ip)

        for srcIP in hostIPs:
            for dstIP in hostIPs:

                if srcIP == dstIP:
                    continue
    
                forwardingCmds = []
                # Only VNF in the Service Chain 
                if len(sla.vnfInputList) == 1:
                    forwardingCmds = self.generateForwardingCommand(cont_name, srcIP, dstIP)

                # Long Chain
                # First VNF should handle Source MACs 
                elif serviceChainIndex == 0:
                    # Forward to Next VNF in the chain
                    nextVNFInfo = gUsedVNFIds[sla.VNFIds[1]]
                    nextVNFIP   = nextVNFInfo.ipAddr

                    for srcIP in hostIPs:
                        forwardingCmds = self.generateForwardingCommand(cont_name, srcIP, nextVNFIP)

                # Last VNF should handle Dest MACs
                elif serviceChainIndex == len(sla.vnfInputList)-1:
                    # Forward to Next VNF in the chain
                    prevVNFInfo = gUsedVNFIds[sla.VNFIds[-2]]
                    prevVNFIP   = prevVNFInfo.ipAddr

                    for dstIP in hostIPs:
                        forwardingCmds = self.generateForwardingCommand(cont_name, prevVNFIP, dstIP)

                # Intermediate VNF of the Service Chain
                else:
                    prevVNFInfo = gUsedVNFIds[sla.VNFIds[serviceChainIndex-1]]
                    prevVNFIP   = prevVNFInfo.ipAddr

                    nextVNFInfo = gUsedVNFIds[sla.VNFIds[serviceChainIndex+1]]
                    nextVNFIP   = nextVNFInfo.ipAddr

                    forwardingCmds = self.generateForwardingCommand(cont_name, prevVNFIP, nextVNFIP)
                    
                for cmd in forwardingCmds:
                    msgs.append(cmd)

        src1 = "192.168.111.11"
        src2 = "192.168.111.21"

        if cont_ip == "192.168.111.50":
            nextIP = "192.168.111.51"

            msgs.append("docker exec %s iptables -t nat -A PREROUTING -s %s -j DNAT --to-destination %s" % (cont_name, src1, nextIP))
            #msgs.append("docker exec %s iptables -t nat -A PREROUTING -s %s -j DNAT --to-destination %s" % (cont_name, nextIP, src1))
            #msgs.append("docker exec %s iptables -t nat -A POSTROUTING -s %s -j SNAT --to-source %s" % (cont_name, nextIP, src1))

        elif cont_ip == "192.168.111.51":
            prevIP = "192.168.111.50"
            #msgs.append("docker exec %s iptables -A FORWARD -s %s -d %s -j ACCEPT" % (cont_name, src1, src2))
            msgs.append("docker exec %s iptables -t nat -A PREROUTING -s %s -j DNAT --to-destination %s" % (cont_name, src1, src2))

            #msgs.append("docker exec %s iptables -t nat -A PREROUTING -s %s -j DNAT --to-destination %s" % (cont_name, prevIP, src2))
            #msgs.append("docker exec %s iptables -t nat -A PREROUTING -s %s -j DNAT --to-destination %s" % (cont_name, src2, prevIP))
            #msgs.append("docker exec %s iptables -t nat -A POSTROUTING -s %s -j SNAT --to-source %s" % (cont_name, src2, prevIP))
        '''

        msgs.append("docker exec %s iptables -A FORWARD -i eth0 -o eth0 -j ACCEPT" % cont_name)

        # Send Messages to Hypervisor
        for msg in msgs:
            sockfd.send(msg)
            hub.sleep(0.3)

    # Installs VNFs at their respective Hypervisors
    # Used only during Placement Algorithm
    def installVNFsAtHypervisors(self, sla, toBeInstalledVNFInfo):

        ## Step - 1: Start Msg Command
        for vnfInfo in toBeInstalledVNFInfo:

            # Retrieve Hypervisor IP
            hypIPAddr = self.m_dpid_to_hyp_ip[vnfInfo.dpid]
            sockfd    = ""

            for pair in self.m_hyp_ip_sockfd_pair:
                if hypIPAddr == pair.val1[0]:
                    sockfd = pair.val2
                    break

            # Sanity Check
            if sockfd == "":
                LOG_DEBUG("%s" % str(self.m_hyp_ip_sockfd_pair))
                LOG_ERROR("Incorrect placement at Hypervisor (%s) or System communication with Hypervisor(%s) is broken." % (vnfInfo.dpid, vnfInfo.dpid))
                return FAILURE

            # Send Commands to Hypervisor System
            self.sendStartVNFCommand(vnfInfo, sockfd)

            # Map VNFInfo to Hypervisor
            # Sanity Check
            if vnfInfo.dpid not in self.m_hypVNFStatus:
                LOG_ERROR("This scenario should not occur. Programming Error!!!")
                return

            # Map VNF Information w.r.t. Hypervisor
            self.m_hypVNFStatus[vnfInfo.dpid].append(vnfInfo.identifier)

        ## Step - 2 : Forwarding Msg Command
        for index in range(0, len(toBeInstalledVNFInfo)):
            vnfInfo = toBeInstalledVNFInfo[index]

            # Retrieve Hypervisor IP
            hypIPAddr = self.m_dpid_to_hyp_ip[vnfInfo.dpid]
            sockfd    = ""

            for pair in self.m_hyp_ip_sockfd_pair:
                if hypIPAddr == pair.val1[0]:
                    sockfd = pair.val2
                    break

            # Sanity Check
            if sockfd == "":
                LOG_ERROR("Incorrect placement at Hypervisor (%s) or System communication with Hypervisor(%s) is broken." % (vnfInfo.dpid, vnfInfo.dpid))
                return FAILURE

            # Forward to Next VNF in the Service Chain
            self.sendForwardingVNFCommand(sla, vnfInfo, sockfd, index)

        return SUCCESS

    # Actual Placement of SLA-defined Flow Rules
    def placementOfSLA(self, sla):

        LOG_INFO("Placement for SLA (%s) started." % sla.identifier)

        ## Step 1: Find Centre for this SLA to place
        ## the 1st VNF of the SLA Service Chain

        # Initialize the 'Seen' DS, 
        # i.e. The list of EndPoints it has seen so far
        seenEndPoints    = {}
        delayFromEndPoint = {}

        # For Every 'vertex' to maintain
        # 1. list of EndPoints it has seen
        # 2. Delay from each End Point
        for datapath in self.m_graph['switches']:
            uVertex = datapath.id
            seenEndPoints[uVertex] = []
            delayFromEndPoint[uVertex] = {}

            for endPointDpid in sla.endPointsDpid:
                delayFromEndPoint[uVertex][endPointDpid] = 0.0

        dctEndPoints = {}

        # For Every 'endPoint' start Dijkstra, iteratively 
        for endPoint in sla.endPointsDpid:
            dctEndPoints[endPoint]              = {}
            dctEndPoints[endPoint]['queue']     = [endPoint]
            dctEndPoints[endPoint]['visited']   = set()
            dctEndPoints[endPoint]['visited'].add(endPoint)
            dctEndPoints[endPoint]['parent']    = {}
            for datapath in self.m_graph['switches']:
                uVertex = datapath.id
                dctEndPoints[endPoint]['parent'][uVertex] = -1
            dctEndPoints[endPoint]['parent'][endPoint] = endPoint
            seenEndPoints[endPoint].append(endPoint)

        queueEndPoints = deque()
        for endDpid in sla.endPointsDpid:
            queueEndPoints.append(endDpid)

        # CPU Mem Requirement of 1st VNF of Chain
        cpuMemReq = sla.vnfCPUMemReq[0]

        # Temporary Information of the VNFs
        toBeInstalledVNFInfo = []

        while len(queueEndPoints):

            endPoint = queueEndPoints.popleft()

            if len(dctEndPoints[endPoint]['queue']):
                uVertex = dctEndPoints[endPoint]['queue'].pop(0)

                for vVertex in self.m_graph['edges'][uVertex]:

                    # Do not consider the Parent vertex
                    if vVertex == dctEndPoints[endPoint]['parent'][uVertex]:
                        continue

                    # Check for constraints
                    if vVertex not in dctEndPoints[endPoint]['visited'] and endPoint not in seenEndPoints[vVertex]:

                        # 'C1' (Dynamic Constraint) - Constraint for Edge's Latency/Delay

                        # Retreive Link latency
                        linkLatency = 0.0
                        if uVertex in self.m_linkLatencyStats and vVertex in self.m_linkLatencyStats[uVertex]:
                            linkLatency = self.m_linkLatencyStats[uVertex][vVertex]['data']

                        elif vVertex in self.m_linkLatencyStats and uVertex in self.m_linkLatencyStats[vVertex]:
                            linkLatency = self.m_linkLatencyStats[vVertex][uVertex]['data']

                        if delayFromEndPoint[uVertex][endPoint] + linkLatency <= sla.delayTolerated :
                            delayFromEndPoint[vVertex][endPoint] = delayFromEndPoint[uVertex][endPoint] + linkLatency

                        else:
                            continue
               
                        # 'C2' (Static Constraint)  : Constraint for CPU utilization 
                        if cpuMemReq > (self.m_hypervisorMemStats[vVertex]['capacity'] - self.m_hypervisorMemStats[vVertex]['used']):
                            continue

                        # 'C3' (Dynamic Constraint) : Constraint for Link's Available BW
                        uVertex_to_vVertexPort = self.m_graph['edges'][uVertex][vVertex]
                        linkBandwidthAchieved  = self.m_switchFlowStats[uVertex][uVertex_to_vVertexPort]['data'][1]

                        if sla.reqBW > LINK_BW_THRESHOLD * (LINK_BW_LIMIT - linkBandwidthAchieved):
                            continue
                
                        dctEndPoints[endPoint]['visited'].add(vVertex)

                        # Add EndPoint to Seen DS
                        seenEndPoints[vVertex].append(endPoint)

                        # Update Parent Pointer
                        dctEndPoints[endPoint]['parent'][vVertex] = uVertex

                        # Push into the Queue 
                        dctEndPoints[endPoint]['queue'].append(vVertex)

                        # Check whether all End points are observed
                        # CCase
                        # Not choose Cloud as centre during Placement
                        if len(seenEndPoints[vVertex]) == len(sla.endPointsDpid) and vVertex != CLOUD_DPID and vVertex == 3:

                            # Center Found - Eureka!!!
                            sla.centre = vVertex
                            dctEndPoints[endPoint]['queue'] = []
                            queueEndPoints = []

                            # Update CPU Memory Used at Hypervisor
                            self.m_hypervisorMemStats[sla.centre]['used'] += cpuMemReq
                            break

            if len(dctEndPoints[endPoint]['queue']):
                queueEndPoints.append(endPoint)

        if sla.centre == -1:
            # TODO : Moving SLA to the Cloud
            pdb.set_trace()
            LOG_DEBUG("SLA (%s) cannot be placed in the Current Network. Moving the entire SLA to the Cloud." % sla.identifier)
            return

        sla.pathToCentre = self.getPathFromCentreToAllEndPoints(sla, dctEndPoints)

        # 1st VNF of the SLA Chain
        toBeInstalledVNFInfo.append(self.assignVNFResources(sla, 0, sla.centre, False))
        sla.pathOfServiceChain.append(sla.centre)
        sla.VNFsNetworkDpid.append(sla.centre)

        # Hardcoded VLAN Start Tag to distinguish between SLAs
        sla.vlanCommonTag = 0x1000 | (sla.identifier << 8)

        # Update Delay Buffer used for future migration purposes
        for item,val in delayFromEndPoint[vVertex].items():

            if val <= sla.delayTolerated:
                sla.delayBuffer = max(sla.delayBuffer, val)
        
        sla.delayBuffer = sla.delayTolerated - sla.delayBuffer

        if sla.delayBuffer == -1.0:
            LOG_ERROR("This scenario should not occur. Programming Error!!!")

            # Recover assigned Resources
            for vnfInfo in toBeInstalledVNFInfo:
                self.recoverVNFResources(sla, vnfInfo)
            return

        # Step 2: Map rest of the VNFs
        lastMappedVNFDpid = sla.centre

        if len(sla.vnfInputList) > 1: # Service Chain

            for index in range(1, len(sla.vnfInputList)):

                dpid      = lastMappedVNFDpid
                slaType   = sla.vnfInputList[index]
                cpuMemReq = sla.vnfCPUMemReq[index]
                
                # Case 1 : Map to the same Hypervisor, if possible
                # Assuming, Link Bandwidth and Link Latency within the Hypervisor is infinite and zero, respectively
                # 'C1' (Static Constraint)  : Constraint for CPU utilization 
                # TODO: ACase
                if False and cpuMemReq <= (self.m_hypervisorMemStats[dpid]['capacity'] - self.m_hypervisorMemStats[dpid]['used']):

                    toBeInstalledVNFInfo.append(self.assignVNFResources(sla, index, dpid, False))
                    
                # Case 2 : Map to neighbors within Link Latency constraints
                else:

                    # 'C1' (Dynamic Constraint) - Constraint for Edge's Latency/Delay
                    # Retreive Link latency
                    nbr_latency = {}
                    # TODO PCase :
                    for nbr_dpid in self.m_graph['edges'][dpid]:

                        # Do not map any VNF at the cloud
                        if nbr_dpid == CLOUD_DPID:
                            continue

                        linkLatency = 0.0
                        # TODO : ACase
                        if nbr_dpid == 4:
                            continue

                        if dpid in self.m_linkLatencyStats and nbr_dpid in self.m_linkLatencyStats[dpid]:
                            linkLatency = self.m_linkLatencyStats[dpid][nbr_dpid]['data']

                        elif nbr_dpid in self.m_linkLatencyStats and dpid in self.m_linkLatencyStats[nbr_dpid]:
                            linkLatency = self.m_linkLatencyStats[nbr_dpid][dpid]['data']

                        # Check within Delay Buffer of SLA
                        if sla.delayBuffer < linkLatency:
                            continue

                        # 'C2' (Static Constraint)  : Constraint for CPU utilization 
                        if cpuMemReq > (self.m_hypervisorMemStats[nbr_dpid]['capacity'] - self.m_hypervisorMemStats[nbr_dpid]['used']):
                            continue

                        # 'C3' (Dynamic Constraint) : Constraint for Link's Available BW
                        dpid_to_nbrDpid_port = self.m_graph['edges'][dpid][nbr_dpid]
                        linkBandwidthAchieved  = self.m_switchFlowStats[uVertex][dpid_to_nbrDpid_port]['data'][1]

                        if sla.reqBW > LINK_BW_THRESHOLD * (LINK_BW_LIMIT - linkBandwidthAchieved):
                            continue

                        # All Constraints satisfied...
                        nbr_latency[nbr_dpid] = linkLatency

                    # Sanity Check
                    if len(nbr_latency) == 0:
                        LOG_DEBUG("VNF(%s) of SLA (%s) cannot be placed at any Nbrs of %s." % (index, sla.identifier, dpid))
                        LOG_DEBUG("SLA (%s) cannot be placed in the Current Network. Moving the entire SLA to the Cloud." % (sla.identifier))

                        # Recover assigned Resources
                        for vnfInfo in toBeInstalledVNFInfo:
                            self.recoverVNFResources(sla, vnfInfo)
                        return                      

                    # Greedy Approach : Choose the Neighbor with minimum Latency
                    minLatency = float("inf")
                    for nbr_dpid, linkLatency in nbr_latency.items():

                        if linkLatency < minLatency:
                            minLatency    = linkLatency
                            selected_dpid = nbr_dpid

                    # Sanity Check
                    if minLatency == float("inf"):
                        LOG_ERROR("This scenario should not occur. Programming Error!!!")
                        LOG_DEBUG("SLA (%s) cannot be placed in the Current Network. Moving the entire SLA to the Cloud." % (sla.identifier))

                        # Recover assigned Resources
                        for vnfInfo in toBeInstalledVNFInfo:
                            self.recoverVNFResources(sla, vnfInfo)
                        
                        return

                    # Update Information about the VNF
                    sla.delayBuffer = sla.delayBuffer - minLatency
                    lastMappedVNFDpid = selected_dpid

                    toBeInstalledVNFInfo.append(self.assignVNFResources(sla, index, selected_dpid, False))
        
                sla.VNFsNetworkDpid.append(lastMappedVNFDpid)
                sla.pathOfServiceChain.append(lastMappedVNFDpid)
            
            LOG_INFO("SLA (%s) Placed at Hypervisor(s) (%s) with overall Delay Buffer (%s)." % (sla.identifier, sla.pathOfServiceChain, sla.delayBuffer))

        # Step 3: Install VNF's of the SLA at their assigned Hypervisor's
        if FAILURE == self.installVNFsAtHypervisors(sla, toBeInstalledVNFInfo):

            LOG_DEBUG("SLA (%s) cannot be placed in the Current Network. System issue!!!" % (sla.identifier))

            # Recover assigned Resources
            for vnfInfo in toBeInstalledVNFInfo:
                self.recoverVNFResources(sla, vnfInfo)
                
            return

        # Yes Yes Yes... SLA is properly installed over the Network
        sla.isInstalled = True

        vnfsMACAddr = []
        for vnfInfo in toBeInstalledVNFInfo:
            vnfsMACAddr.append(vnfInfo.macAddr)

        # Note the complete path of the SLA in the network for all Hosts in the SLA
        sla.compPathOfSLA = self.retreivePathOfSLA(sla)

        # Step 4: Installation of the respective flow Rules will be done here
        self.updateNewSLAFlowRules(sla, True, [], [])

        LOG_INFO("SLA (%s) is installed over the Network with the VNFs placed at"
                  " Hypervisors (%s) having MAC addresses (%s)." % 
                  (sla.identifier, sla.pathOfServiceChain, vnfsMACAddr))

        # Tweak : MCase Node Bottleneck
        global gNodeBottleneckHackCount
        if False and gNodeBottleneckHackCount == True:
            gNodeBottleneckHackCount = False
            bottleneckedDpid = 3
            LOG_INFO("Tweaked Bottleneck detected at Hypervisor(%s)." % bottleneckedDpid)
            self.handleNodeBottleneck(bottleneckedDpid)

    # Removes consecutive duplicates from Path of Service Chain
    # e.g. Input  - 2 3 3 4 5 5 5 6
    #      Output - [[2 1] [3 2] [4 1] [5 3] [6 1]]
    def convertPathOfServiceChain(self, inList):

        outList = []

        outListLen = 1
        outList.append([inList[0], outListLen])

        for index in range(1, len(inList)):
            if outList[outListLen-1][0] == inList[index]:
                outList[outListLen-1][1] += 1

            else:
                outList.append([inList[index], 1])
                outListLen += 1

        return outList

    # Retreives the complete Path of the SLA in the Network
    def retreivePathOfSLA(self, sla):

        allPaths = {}

        for src_mac in sla.endUsersMac:
            for dst_mac in sla.endUsersMac:

                # Sanity Check
                if src_mac == dst_mac:
                    continue

                path = []

                src_mac  = src_mac
                dst_mac  = dst_mac

                src_dpid = self.m_mac_to_dpid_port[src_mac].val1
                dst_dpid = self.m_mac_to_dpid_port[dst_mac].val1

                flowpath_src_to_centre = sla.pathToCentre[src_dpid]
                flowpath_src_to_centre = list(reversed(flowpath_src_to_centre))        

                # -1 indicates an End-Point
                path = [[flowpath_src_to_centre[0], -1]] # Source Hypervisor

                # Intermediate Switches between {Src Host to Centre} 
                if len(flowpath_src_to_centre) > 2:
                    for index in range(1, len(flowpath_src_to_centre) - 1):
                        path.append([flowpath_src_to_centre[index], 0])

                # Path of the Service Chain
                midPathOfServiceChain = self.convertPathOfServiceChain(sla.pathOfServiceChain)
                for item in midPathOfServiceChain:
                    path.append(item)

                flowpath_last_to_dst = self.getSrcToDestPath(sla.pathOfServiceChain[-1], dst_dpid)
                
                # Intermediate Switches between {Last VNF and Dst}
                if len(flowpath_last_to_dst) > 2:
                    for index in range(1, len(flowpath_last_to_dst) - 1):
                        path.append([flowpath_last_to_dst[index], 0])

                # -1 indicates an End-Point
                path.append([flowpath_last_to_dst[-1], -1]) # Destination Hypervisor

                # Complete Path of SLA from Srouce to Destination
                if src_mac not in allPaths:
                    allPaths[src_mac] = {}

                if dst_mac not in allPaths[src_mac]:
                    allPaths[src_mac][dst_mac] = {}

                allPaths[src_mac][dst_mac]['prevPath'] = []
                allPaths[src_mac][dst_mac]['currPath'] = path
                allPaths[src_mac][dst_mac]['priority'] = START_PRIORITY_VAL
 
                # Path of SLA Chain
                if self.debugFlag:
                    LOG_INFO("SLA Complete Path (Src %s to Dst %s) : %s"  % (src_dpid, dst_dpid, path))

        return allPaths

    # Installs the Flow Rules w.r.t. SLA using Hard Timeout
    def installSLAFlowRules(self, sla, src_mac, dst_mac, msg, ofproto, parser, pkt_in_port, src_ip, dst_ip, priority):

        processed_vnf_cnt = 0

        ## 1. Actor - Ingress Switch via In-between Switches
        src_dpid    = self.m_mac_to_dpid_port[src_mac].val1
        flowpath_src_to_centre = sla.pathToCentre[src_dpid]
        flowpath_src_to_centre = list(reversed(flowpath_src_to_centre))

        centre_dpid = sla.VNFsNetworkDpid[0]
        prev_switch = src_dpid
      
        # TODO: Src End point and 1st VNF at the same place

        # Packet reaches from End-point (Src. Point) to the 1st VNF (centre)
        if len(flowpath_src_to_centre) != 1:

            for i in range(1, len(flowpath_src_to_centre)-1):

                this_dpid   = flowpath_src_to_centre[i]
                datapath    = self.getDatapath(this_dpid)
                next_switch = flowpath_src_to_centre[i+1]

                out_port    = self.m_graph['edges'][this_dpid][next_switch]
                in_port     = self.m_graph['edges'][this_dpid][prev_switch]

                match       = parser.OFPMatch(vlan_vid=(sla.vlanCommonTag | processed_vnf_cnt), in_port=in_port, eth_src=src_mac, eth_dst=dst_mac)
                actions     = [parser.OFPActionOutput(out_port)]
                self.add_flow(datapath, priority, match, actions)
                LOG_DEVEL("Datapath : %s | Match : vlan_tag-%s in_port-%s eth_src-%s eth_dst-%s | Output : out_port-%s" % (this_dpid, sla.vlanCommonTag | processed_vnf_cnt, in_port, src_mac, dst_mac, out_port))

                prev_switch = this_dpid
    
        ## 2. Actor - All the VNFs of the Service Chain
        ## Packet starts processing from 1st VNF to the rest of the VNF(s), if any
        flowpath_start_to_last = sla.pathOfServiceChain
        prev_in_port = pkt_in_port

        if len(flowpath_start_to_last):

            # Check whether multiple VNF(s) are connected to the same Hypervisor
            isMultipleVNFsAtSameDpid = False

            for i in range(0, len(flowpath_start_to_last)):

                this_dpid   = flowpath_start_to_last[i]
                datapath    = self.getDatapath(this_dpid)
                in_port     = self.m_graph['edges'][this_dpid][prev_switch] if this_dpid != prev_switch else prev_in_port

                if i != len(flowpath_start_to_last)-1:
                    next_switch = flowpath_start_to_last[i+1]
                    out_port    = ofproto.OFPP_IN_PORT if this_dpid == next_switch else self.m_graph['edges'][this_dpid][next_switch]

                # If installed VNF's dpid
                if this_dpid == sla.VNFsNetworkDpid[processed_vnf_cnt]:

                    # Change dst_Mac to mac_address of the VNF
                    vnf_mac      = sla.VNFsNetworkMac[processed_vnf_cnt]
                    vnf_out_port = self.m_mac_to_dpid_port[vnf_mac].val2
                    vnf_out_port = ofproto.OFPP_IN_PORT if vnf_out_port == in_port else vnf_out_port

                    # If multiple VNFs at same Hypervisor
                    if isMultipleVNFsAtSameDpid:
                        # Do nothing, Packet sent in previous iteration
                        isMultipleVNFsAtSameDpid = False                        

                    # Receiving Packet for first time
                    elif this_dpid == prev_switch:
                        match   = parser.OFPMatch(in_port=in_port,eth_src=src_mac,eth_dst=dst_mac)
                        actions = [parser.OFPActionSetField(eth_src=self.m_ovs_mac[this_dpid]),
                                   parser.OFPActionSetField(eth_dst=vnf_mac),
                                   parser.OFPActionOutput(vnf_out_port)]

                        self.add_flow(datapath, priority, match, actions)
                        LOG_DEVEL("Datapath : %s | Match : in_port-%s eth_src-%s eth_dst-%s | SetFeild : eth_dst - %s, Output : out_port-%s" % (this_dpid, in_port, src_mac, dst_mac, vnf_mac, vnf_out_port))

                    else:
                        # Check VLAN Tag
                        match   = parser.OFPMatch(vlan_vid=(sla.vlanCommonTag | processed_vnf_cnt),in_port=in_port,eth_src=src_mac,eth_dst=dst_mac)
                        actions = [parser.OFPActionPopVlan(0x8100),
                                   parser.OFPActionSetField(eth_src=self.m_ovs_mac[this_dpid]),
                                   parser.OFPActionSetField(eth_dst=vnf_mac),
                                   parser.OFPActionOutput(vnf_out_port)]

                        self.add_flow(datapath, priority, match, actions)
                        LOG_DEVEL("Datapath : %s | Match : vlan_vid-%s in_port-%s eth_src-%s eth_dst-%s | SetFeild : eth_dst - %s, Output : out_port-%s" % (this_dpid, sla.vlanCommonTag | processed_vnf_cnt, in_port, src_mac, dst_mac, vnf_mac, vnf_out_port))

                    processed_vnf_cnt += 1
                   
                    # Packet receiving from Last VNF
                    # Scenario Handled in next Section.
                    if i == len(flowpath_start_to_last) - 1:
                        break

                    # Re-direct the packet received from the VNF through the Service Chain/Destination
                    match = parser.OFPMatch(in_port=vnf_out_port, eth_src=vnf_mac, eth_dst=dst_mac)

                    # Next VNF at the same Hypervisor
                    if this_dpid == next_switch:
                        out_port     = ofproto.OFPP_IN_PORT
                        next_vnf_mac = sla.VNFsNetworkMac[processed_vnf_cnt]
                        actions      = [parser.OFPActionSetField(eth_src=src_mac),
                                        parser.OFPActionSetField(eth_dst=next_vnf_mac),
                                        parser.OFPActionOutput(out_port)]

                        isMultipleVNFsAtSameDpid = True
                        LOG_DEVEL("Datapath : %s | Match : in_port-%s eth_src-%s eth_dst-%s | SetFeild : eth_src - %s, eth_dst-%s Output : out_port-%s" % (this_dpid, vnf_out_port, vnf_mac, dst_mac, src_mac, next_vnf_mac, out_port))

                    else:
                        # Add VLAN Tag for processing in next Switch(s)
                        out_port = self.m_graph['edges'][this_dpid][next_switch]
                        actions  = [parser.OFPActionPushVlan(0x8100),
                                    parser.OFPActionSetField(vlan_vid=(sla.vlanCommonTag | processed_vnf_cnt)),
                                    parser.OFPActionSetField(eth_src=src_mac),
                                    parser.OFPActionOutput(out_port)]

                        LOG_DEVEL("Datapath : %s | Match : in_port-%s eth_src-%s eth_dst-%s | SetFeild : vlan_tag-%s, eth_src - %s, Output : out_port-%s" % (this_dpid, vnf_out_port, vnf_mac, dst_mac, sla.vlanCommonTag | processed_vnf_cnt, src_mac, out_port))

                    self.add_flow(datapath, priority, match, actions)
                    

                # Intermediate Switches
                else:
                    match    = parser.OFPMatch(vlan_vid=(sla.vlanCommonTag | processed_vnf_cnt), in_port=in_port, eth_src=src_mac, eth_dst=dst_mac)
                    actions  = [parser.OFPActionOutput(out_port)]
                    self.add_flow(datapath, priority, match, actions)
                    LOG_DEVEL("Datapath : %s | Match : vlan_tag-%s in_port-%s eth_src-%s eth_dst-%s | Output : out_port-%s" % (this_dpid, sla.vlanCommonTag | processed_vnf_cnt, in_port, src_mac, dst_mac, out_port))

                prev_switch = this_dpid
    
        ## 3. Actor - Last VNF and Intermediate Switches
        # Re-direct the packet from Last VNF to the Egress Point (Actual Dest. Point)
        last_vnf_mac  = sla.VNFsNetworkMac[processed_vnf_cnt  - 1]
        last_vnf_dpid = sla.VNFsNetworkDpid[processed_vnf_cnt - 1]
        
        flowpath_last_to_dst = self.getSrcToDestPath(last_vnf_dpid, self.m_mac_to_dpid_port[dst_mac].val1)
        dst_dpid = self.m_mac_to_dpid_port[dst_mac].val1

        ## Case 3a. Destination VNF Hypervisor is also connected to the Egress Switch
        if len(flowpath_last_to_dst) == 0:

            # Re-direct the packet from the VNF towards the destination
            datapath  = self.getDatapath(dst_dpid)
            same_port = self.m_mac_to_dpid_port[dst_mac].val2
            match     = parser.OFPMatch(in_port=same_port, eth_src=last_vnf_mac, eth_dst=dst_mac)
            actions   = [parser.OFPActionSetField(eth_src=src_mac),
                         parser.OFPActionOutput(ofproto.OFPP_IN_PORT)]
            self.add_flow(datapath, priority, match, actions)
            LOG_DEVEL("Datapath : %s | Match : in_port-%s eth_src-%s eth_dst-%s | SetFeild : eth_src - %s, Output : out_port-%s" % (dst_dpid, same_port, last_vnf_mac, dst_mac, src_mac, ofproto.OFPP_IN_PORT))

        ## Case 3b. Last VNF Hypervisor and Egress Switch are not same
        else:
            last_vnf_in_port = self.m_dpid_to_mac_port[last_vnf_dpid][last_vnf_mac]

            for i in range(0, len(flowpath_last_to_dst)-1):

                this_dpid   = flowpath_last_to_dst[i]
                datapath    = self.getDatapath(this_dpid)
                next_switch = flowpath_last_to_dst[i+1]
                in_port     = last_vnf_in_port if i == 0 else self.m_graph['edges'][this_dpid][prev_switch]
                out_port    = self.m_graph['edges'][this_dpid][next_switch]
                out_port    = ofproto.OFPP_IN_PORT if out_port == in_port else out_port

                # Re-format the packet from the Last VNF towards the actual destination
                if this_dpid == last_vnf_dpid:
                    match   = parser.OFPMatch(in_port=in_port, eth_src=last_vnf_mac, eth_dst=dst_mac)
                    # Add VLAN Tag for processing in the last Switch
                    actions = [parser.OFPActionPushVlan(0x8100),
                               parser.OFPActionSetField(vlan_vid=(sla.vlanCommonTag | processed_vnf_cnt)),
                               parser.OFPActionSetField(eth_src=src_mac),
                               parser.OFPActionOutput(out_port)]
                    self.add_flow(datapath, priority, match, actions)
                    LOG_DEVEL("Datapath : %s | Match : in_port-%s eth_src-%s eth_dst-%s | SetFeild : vlan_tag-%s eth_src - %s, Output : out_port-%s" % (this_dpid, in_port, last_vnf_mac, dst_mac, sla.vlanCommonTag | processed_vnf_cnt, src_mac, out_port))

                # Intermediate Switches
                else:
                    match    = parser.OFPMatch(vlan_vid=(sla.vlanCommonTag | processed_vnf_cnt), in_port=in_port, eth_src=src_mac, eth_dst=dst_mac)
                    actions  = [parser.OFPActionOutput(out_port)]
                    self.add_flow(datapath, priority, match, actions)
                    LOG_DEVEL("Datapath : %s | Match : vlan_tag-%s in_port-%s eth_src-%s eth_dst-%s | Output : out_port-%s" % (this_dpid, sla.vlanCommonTag | processed_vnf_cnt, in_port, src_mac, dst_mac, out_port))

                prev_switch = this_dpid
        
        ## Case 4. Actor - Egress Switch
        if len(flowpath_last_to_dst) != 1:
            datapath = self.getDatapath(dst_dpid)
            in_port  = self.m_graph['edges'][dst_dpid][prev_switch]
            out_port = self.m_mac_to_dpid_port[dst_mac].val2
            match    = parser.OFPMatch(vlan_vid=(sla.vlanCommonTag | processed_vnf_cnt), in_port=in_port, eth_dst=dst_mac)
            actions  = [parser.OFPActionPopVlan(0x8100),
                        parser.OFPActionOutput(out_port)]
            self.add_flow(datapath, priority, match, actions)
            LOG_DEVEL("Datapath : %s | Match : vlan_tag-%s in_port-%s eth_dst-%s | Output : out_port-%s" % (dst_dpid, sla.vlanCommonTag | processed_vnf_cnt, in_port, dst_mac, out_port))

        ## 5. Actor - Ingress Switch
        # Case 5a. Ingrees Switch and Centre Switch are not same
        if len(flowpath_src_to_centre) != 1:

            datapath    = self.getDatapath(src_dpid)
            next_switch = flowpath_src_to_centre[1]
            out_port    = self.m_graph['edges'][src_dpid][next_switch]
            match       = parser.OFPMatch(in_port=pkt_in_port, eth_src=src_mac, eth_dst=dst_mac)
            # Add VLAN Tag for processing in next Switch(s)
            actions     = [parser.OFPActionPushVlan(0x8100),
                           parser.OFPActionSetField(vlan_vid=sla.vlanCommonTag),
                           parser.OFPActionOutput(out_port)]

            if pkt_in_port == out_port:
                return

            self.add_flow(datapath, priority, match, actions) # Flow-Mod
            LOG_DEVEL("Datapath : %s | Match : in_port-%s eth_src-%s eth_dst-%s | Output : vlan_vid-%s out_port-%s" % (src_dpid, pkt_in_port, src_mac, dst_mac, sla.vlanCommonTag, out_port))

            data    = msg.data if msg.buffer_id == ofproto.OFP_NO_BUFFER else None
            out_msg = datapath.ofproto_parser.OFPPacketOut(datapath=datapath, buffer_id=msg.buffer_id, in_port=pkt_in_port, actions=actions, data=data)
            LOG_DEBUG("PacketOUT - Datapath : %s | Match : in_port-%s eth_src-%s eth_dst-%s | Output : vlan_vid-%s out_port-%s" % (src_dpid, pkt_in_port, src_mac, dst_mac, sla.vlanCommonTag, out_port))
            datapath.send_msg(out_msg) # Packet-Out

        # Case 5b:(Special) Handling Packet-Out when Src-switch and Centre-Switch are the same
        # Flow-mod is handled earlier for this scenario
        else:
            vnf_mac   = sla.VNFsNetworkMac[0]
            same_port = self.m_mac_to_dpid_port[vnf_mac].val2
            actions   = [parser.OFPActionSetField(eth_src=self.m_ovs_mac[this_dpid]),
                         parser.OFPActionSetField(eth_dst=vnf_mac),
                         parser.OFPActionOutput(ofproto.OFPP_IN_PORT)]

            data    = msg.data if msg.buffer_id == ofproto.OFP_NO_BUFFER else None
            out_msg = datapath.ofproto_parser.OFPPacketOut(datapath=datapath, buffer_id=msg.buffer_id, in_port=pkt_in_port, actions=actions, data=data)
            LOG_DEBUG("PacketOUT - Datapath : %s | Match : in_port-%s eth_src-%s eth_dst-%s | SetFeild : eth_dst - %s, Output : out_port-%s" % (this_dpid, pkt_in_port, src_mac, dst_mac, vnf_mac, vnf_out_port))
            datapath.send_msg(out_msg) # Packet-Out


    # Removes Flow Rule entries for the input path
    def removeOldSLAFlowRules(self, sla, src_mac, dst_mac, path, oldVNFsNetworkDpid, oldVNFsNetworkMac):

        # Sanity Check
        if path == []:
            return

        priority = sla.compPathOfSLA[src_mac][dst_mac]['priority'] - 1

        # Delete Flow for the Old/Previous Path
                    
        processed_vnf_cnt = 0

        src_dpid    = self.m_mac_to_dpid_port[src_mac].val1
        dst_dpid    = self.m_mac_to_dpid_port[dst_mac].val1
        src_in_port = self.m_mac_to_dpid_port[src_mac].val2

        ## 1. Actor - Ingress Switch via In-between Switches
        prev_switch = src_dpid
        slaIndex = 1

        while slaIndex < len(path):

            # Pair contains [dpid, Information]
            # Information : {-1 : End Point, 0 : Intermediate Switch, <Num> : No. of VNFs isntalled}
            pair = path[slaIndex]

            # Reached the Switch with the First VNF installed
            if pair[1] != 0:
                break

            this_dpid   = pair[0]
            datapath    = self.getDatapath(this_dpid)
            parser      = datapath.ofproto_parser
            ofproto     = datapath.ofproto
            next_switch = path[slaIndex + 1][0]

            # Assuming Hosts connected to the Hypervisor's
            in_port     = self.m_graph['edges'][this_dpid][prev_switch] if this_dpid != prev_switch else src_in_port
            out_port    = ofproto.OFPP_IN_PORT if this_dpid == next_switch else self.m_graph['edges'][this_dpid][next_switch]

            match       = parser.OFPMatch(vlan_vid=(sla.vlanCommonTag | processed_vnf_cnt), in_port=in_port, eth_src=src_mac, eth_dst=dst_mac)
            self.del_flow(datapath, priority, match)
            LOG_DEVEL("Removed Datapath : %s | Match : vlan_tag-%s in_port-%s eth_src-%s eth_dst-%s | Output : out_port-%s" % (this_dpid, sla.vlanCommonTag | processed_vnf_cnt, in_port, src_mac, dst_mac, out_port))

            prev_switch = this_dpid
            slaIndex   += 1

        ## 2. Actor - All the VNFs of the Service Chain
        ## Packet starts processing from 1st VNF to the rest of the VNF(s), if any
        prev_in_port = src_in_port

        # Check and count whether multiple VNF(s) are connected to the same Hypervisor
        isMultipleVNFsAtSameDpid = path[slaIndex][1] - 1

        while True:
            
            this_dpid    = path[slaIndex][0]
            datapath     = self.getDatapath(this_dpid)
            parser       = datapath.ofproto_parser
            ofproto      = datapath.ofproto
            in_port      = self.m_graph['edges'][this_dpid][prev_switch] if this_dpid != prev_switch else prev_in_port
            prev_in_port = in_port

            next_switch  = path[slaIndex + 1][0]
            out_port     = ofproto.OFPP_IN_PORT if this_dpid == next_switch else self.m_graph['edges'][this_dpid][next_switch]

            # VNF installed over this dpid
            if path[slaIndex][1] != 0:

                # Change dst_Mac to mac_address of the VNF
                vnf_mac      = oldVNFsNetworkMac[processed_vnf_cnt]
                vnf_out_port = self.m_mac_to_dpid_port[vnf_mac].val2
                vnf_out_port = ofproto.OFPP_IN_PORT if vnf_out_port == in_port else vnf_out_port
            
                # If multiple VNFs at same Hypervisor
                if isMultipleVNFsAtSameDpid:
                    # Do nothing, Packet sent in previous iteration
                    LOG_DEVEL("Handling Multiple Consecutive VNFs at the Same Hypervisor %s" % this_dpid)

                # Receiving Packet for first time
                elif this_dpid == prev_switch:
                    match = parser.OFPMatch(in_port=in_port, eth_src=src_mac, eth_dst=dst_mac)
                    self.del_flow(datapath, priority, match)
                    LOG_DEVEL("Removed Datapath : %s | Match : in_port-%s eth_src-%s eth_dst-%s | SetFeild : eth_dst - %s, Output : out_port-%s" % (this_dpid, in_port, src_mac, dst_mac, vnf_mac, vnf_out_port))

                else:
                    # Check VLAN Tag
                    match = parser.OFPMatch(vlan_vid=(sla.vlanCommonTag | processed_vnf_cnt),in_port=in_port,eth_src=src_mac,eth_dst=dst_mac)
                    self.del_flow(datapath, priority, match)
                    LOG_DEVEL("Removed Datapath : %s | Match : vlan_vid-%s in_port-%s eth_src-%s eth_dst-%s | SetFeild : eth_src - %s, eth_dst - %s, Output : out_port-%s" % (this_dpid, sla.vlanCommonTag | processed_vnf_cnt, in_port, src_mac, dst_mac, self.m_ovs_mac[this_dpid], vnf_mac, vnf_out_port))

                processed_vnf_cnt += 1
                prev_switch = this_dpid

                # Packet receiving from Last VNF
                # Scenario Handled in next Section.
                # All VNF(s) have been processed
                if processed_vnf_cnt == len(sla.VNFsNetworkDpid):
                    break

                # Re-direct the packet received from the VNF through the Service Chain/Destination
                match = parser.OFPMatch(in_port=vnf_out_port, eth_src=vnf_mac, eth_dst=dst_mac)

                # Next VNF at the same Hypervisor
                if this_dpid == next_switch:
                    out_port     = ofproto.OFPP_IN_PORT
                    next_vnf_mac = oldVNFsNetworkMac[processed_vnf_cnt - 1]

                    LOG_DEVEL("Removed Datapath : %s | Match : in_port-%s eth_src-%s eth_dst-%s | SetFeild : eth_src - %s, eth_dst-%s Output : out_port-%s" % (this_dpid, vnf_out_port, vnf_mac, dst_mac, src_mac, next_vnf_mac, out_port))

                else:
                    # Add VLAN Tag for processing in next Switch(s)
                    out_port = self.m_graph['edges'][this_dpid][next_switch]
                    LOG_DEVEL("Removed Datapath : %s | Match : in_port-%s eth_src-%s eth_dst-%s | SetFeild : vlan_tag-%s, eth_src - %s, Output : out_port-%s" % (this_dpid, vnf_out_port, vnf_mac, dst_mac, sla.vlanCommonTag | processed_vnf_cnt, src_mac, out_port))

                self.del_flow(datapath, priority, match)
                    

            # Intermediate Switches
            else:
                match   = parser.OFPMatch(vlan_vid=(sla.vlanCommonTag | processed_vnf_cnt),in_port=in_port,eth_src=src_mac,eth_dst=dst_mac)
                self.del_flow(datapath, priority, match)
                LOG_DEVEL("Removed Datapath : %s | Match : vlan_tag-%s in_port-%s eth_src-%s eth_dst-%s | Output : out_port-%s" % (this_dpid, sla.vlanCommonTag | processed_vnf_cnt, in_port, src_mac, dst_mac, out_port))

                prev_switch = this_dpid

            if isMultipleVNFsAtSameDpid == 0:
                slaIndex += 1
            else:
                isMultipleVNFsAtSameDpid -= 1

        ## 3. Actor - Last VNF and Intermediate Switches
        # Re-direct the packet from Last VNF to the Egress Point (Actual Dest. Point)
        last_vnf_mac  = oldVNFsNetworkMac[-1]
        last_vnf_dpid = oldVNFsNetworkDpid[-1]

        ## Case 3a. Destination VNF Hypervisor is also connected to the Egress Switch
        if prev_switch == dst_dpid:

            # Re-direct the packet from the VNF towards the destination
            datapath  = self.getDatapath(dst_dpid)
            parser    = datapath.ofproto_parser
            ofproto   = datapath.ofproto
            same_port = self.m_mac_to_dpid_port[dst_mac].val1
            match     = parser.OFPMatch(in_port=same_port,eth_src=last_vnf_mac,eth_dst=dst_mac)
            self.del_flow(datapath, priority, match)
            LOG_DEVEL("Removed Datapath : %s | Match : in_port-%s eth_src-%s eth_dst-%s | SetFeild : eth_src - %s, Output : out_port-%s" % (dst_dpid, same_port, last_vnf_mac, dst_mac, src_mac, ofproto.OFPP_IN_PORT))

        ## Case 3b. Last VNF Hypervisor and Egress Switch are not same
        else:
            last_vnf_in_port = self.m_dpid_to_mac_port[last_vnf_dpid][last_vnf_mac]

            while path[slaIndex][1] != -1:

                this_dpid   = path[slaIndex][0]
                datapath    = self.getDatapath(this_dpid)
                parser      = datapath.ofproto_parser
                ofproto     = datapath.ofproto
                next_switch = path[slaIndex + 1][0]
                in_port     = last_vnf_in_port if slaIndex == 0 or this_dpid == prev_switch else self.m_graph['edges'][this_dpid][prev_switch]
                out_port    = self.m_graph['edges'][this_dpid][next_switch]
                out_port    = ofproto.OFPP_IN_PORT if out_port == in_port else out_port

                # Re-format the packet from the Last VNF towards the actual destination
                if this_dpid == last_vnf_dpid:
                    match   = parser.OFPMatch(in_port=in_port, eth_src=last_vnf_mac, eth_dst=dst_mac)
                    self.del_flow(datapath, priority, match)
                    LOG_DEVEL("Removed Datapath : %s | Match : in_port-%s eth_src-%s eth_dst-%s | SetFeild : vlan_tag-%s eth_src - %s, Output : out_port-%s" % (this_dpid, in_port, last_vnf_mac, dst_mac, sla.vlanCommonTag | processed_vnf_cnt, src_mac, out_port))

                # Intermediate Switches
                else:
                    match   = parser.OFPMatch(vlan_vid=(sla.vlanCommonTag | processed_vnf_cnt), in_port=in_port, eth_src=src_mac, eth_dst=dst_mac)
                    self.del_flow(datapath, priority, match)
                    LOG_DEVEL("Removed Datapath : %s | Match : vlan_tag-%s in_port-%s eth_src-%s eth_dst-%s | Output : out_port-%s" % (this_dpid, sla.vlanCommonTag | processed_vnf_cnt, in_port, src_mac, dst_mac, out_port))

                prev_switch = this_dpid
                slaIndex   += 1


        ## Case 4. Actor - Egress Switch
        if prev_switch != dst_dpid:
            datapath = self.getDatapath(dst_dpid)
            parser   = datapath.ofproto_parser
            ofproto  = datapath.ofproto
            in_port  = self.m_graph['edges'][dst_dpid][prev_switch]
            out_port = self.m_mac_to_dpid_port[dst_mac].val2
            match    = parser.OFPMatch(vlan_vid=(sla.vlanCommonTag | processed_vnf_cnt), in_port=in_port, eth_dst=dst_mac)
            self.del_flow(datapath, priority, match)
            LOG_DEVEL("Removed Datapath : %s | Match : vlan_tag-%s in_port-%s eth_dst-%s | Output : out_port-%s" % (dst_dpid, sla.vlanCommonTag | processed_vnf_cnt, in_port, dst_mac, out_port))


        ## 5. Actor - Ingress Switch
        # Case 5a. Ingrees Switch and Centre Switch are not same
        if len(path) > 2 and path[0][0] != path[1][0]:

            datapath    = self.getDatapath(src_dpid)
            parser      = datapath.ofproto_parser
            ofproto     = datapath.ofproto
            next_switch = path[1][0]
            out_port    = self.m_graph['edges'][src_dpid][next_switch]
            match       = parser.OFPMatch(in_port=src_in_port, eth_src=src_mac, eth_dst=dst_mac)
            # Add VLAN Tag for processing in next Switch(s)
            if src_in_port == out_port:
                return

            self.del_flow(datapath, priority, match) # Flow-Mod
            LOG_DEVEL("Removed Datapath : %s | Match : in_port-%s eth_src-%s eth_dst-%s | Output : vlan_vid-%s out_port-%s" % (src_dpid, src_in_port, src_mac, dst_mac, sla.vlanCommonTag, out_port))


    # Returns the Path from Source Dpid to the Dest. Dpid
    def getSrcToDestPath(self, src, dst):

        #Sanity Check
        if src == dst:
            return [src]

        path = []

        # Simple BFS on computed Spanning Tree Links
        queue  = deque()
        color  = {}
        parent = {}

        for node in self.m_graph['switches']:
            color[node.id]  = COLOR_WHITE
            parent[node.id] = ""
        
        queue.append(src)
        parent[src] = -1

        while queue:
            u = queue.popleft()
            color[u] = COLOR_BLACK

            #for v, port in self.m_graph['edges'][u].items():
            for v in self.m_spTreeLinks[u]:

                # TODO : Improve by using weights among the edges
                # Boils down to simple BFS
                if color[v] == COLOR_WHITE:
                    parent[v] = u
                    if v == dst:
                        path.append(v)
                        while parent[v] != -1:
                            v = parent[v]
                            path.append(v)
                        break
                    else:
                        color[v] = COLOR_BLACK    
                        queue.append(v)
        
        return list(reversed(path))

    # Retreive Path from the Centre to all End Points
    def getPathFromCentreToAllEndPoints(self, sla, dctEndPoints):

        # This is the entire path from Centre to each EndPoint of the SLA
        pathToCentre = {}

        for endPoint in sla.endPointsDpid:

            pathToCentre[endPoint] = []
            current = sla.centre

            # Traverse parent pointers to reach the EndPoint
            while current != dctEndPoints[endPoint]['parent'][current]:

                pathToCentre[endPoint].append(current)

                if current == -1: # Invalid Parent
                    LOG_ERROR("This scenario should not occur. Programming Error!!!")
                    break

                current = dctEndPoints[endPoint]['parent'][current]

            pathToCentre[endPoint].append(endPoint)

        return pathToCentre


    def get_sla_flow_path(self, src_dpid, dst_dpid, sla):
        
        # Sanity Check
        if sla.isInstalled == 0:
            LOG_ERROR("SLA (%s) is not mapped." % sla.identifier + 1)
            return

        # Algorithm for VNF(s) Placement


    # Returns dpid of the switch to which the host(mac) is connected to
    def get_dpid_from_mac(self, mac):
    
        if mac in self.m_mac_to_dpid_port:
            value = self.m_mac_to_dpid_port[mac]
            return SUCCESS, value.val1

        else:
            return FAILURE,None


    # Checks whether a Switch exists or not
    def IsSwitchExist(self, dpid):

        for dp in self.m_graph['switches']:
            if dp.id == dpid:
                return SUCCESS

        return FAILURE

    
    def getDatapath(self, dpid):
        datapath = None
        # Retreive datapath of 'this_switch'
        for dp in self.m_graph['switches']:
            if dp.id == dpid:
                datapath = dp
                break

        if datapath == None:
            print "********************************"
            LOG_DEBUG("datapath not found , switches:")
            for val in self.m_graph['switches']:
                print val.id
            print "********************************"

        return datapath

    # Switch Enter Event
    @set_ev_cls(event.EventSwitchEnter)
    def update_topology_switchEnter(self, ev):

        if LOGGING_DEBUG:
            LOG_DEBUG("Event: Switch Added")
            
        # Retreive the list of all switches available in the topology
        all_switch_info = get_all_switch(self.m_topology_api_app)

        # Add Switch
        for switch in all_switch_info:
            dpid = switch.dp.id

            if switch.dp not in self.m_graph['switches']:

                # Check whether any VNF is to be installed
                self.m_graph['switches'].add(switch.dp)

                # Assign a MAC address to the OVS for Service chaining
                if dpid not in self.m_ovs_mac:
                    self.m_ovs_mac[dpid] = "00:00:00:%s%s:%s%s:%s%s" % (dpid,dpid,dpid,dpid,dpid,dpid)

                if dpid not in self.m_graph['edges']:
                    self.m_graph['edges'].setdefault(dpid, {})
                if dpid not in self.m_graph['hosts']:
                    self.m_graph['hosts'].setdefault(dpid,{})

                # Initialize Switch-Latency Monitoring
                if dpid not in self.m_switchLatencyStats:
                    self.m_switchLatencyStats[dpid] = {}
                    self.m_switchLatencyStats[dpid]['lastSentTime']   = float(0.0)
                    self.m_switchLatencyStats[dpid]['lastUpdateTime'] = float(0.0)
                    self.m_switchLatencyStats[dpid]['data']           = float(0.0)

                # Initialize CPU Memory Stats
                # TODO : Assuming, a Hypervisor is connected to only one OVS-switch
                if dpid not in self.m_hypervisorMemStats:
                    self.m_hypervisorMemStats[dpid] = {}
                    self.m_hypervisorMemStats[dpid]['capacity'] = ALL_HYPERVISOR_CPU_MEMORY_INIT if dpid != CLOUD_DPID else 100 * ALL_HYPERVISOR_CPU_MEMORY_INIT
                    self.m_hypervisorMemStats[dpid]['used']     = 0

                # Initialize CPU Percent Utilization Stats
                if dpid not in self.m_hypervisorCpuUtilStats:
                    self.m_hypervisorCpuUtilStats[dpid] = {}
                    self.m_hypervisorCpuUtilStats[dpid]['startRcvdTime'] = float(0.0)
                    self.m_hypervisorCpuUtilStats[dpid]['lastRcvdTime']  = float(0.0)
                    self.m_hypervisorCpuUtilStats[dpid]['data']          = float(0.0)

                # Initialize Hypervisor VNF Status
                if dpid not in self.m_hypVNFStatus:
                    self.m_hypVNFStatus[dpid] = []

        # Update network's Spanning Tree
        for datapath in self.m_graph['switches']:
            self._calculate_SpanningTree(datapath.id)
            break

    # Switch Leave event
    @set_ev_cls(event.EventSwitchLeave)
    def update_topology_switchLeave(self, ev):

        if LOGGING_DEBUG:
            LOG_DEBUG("Event: Switch Deleted - Re-calculating Spanning Tree")

        # Retreive the list of all switches available in the topology
        all_switch_info = get_all_switch(self.m_topology_api_app)

        findFlag = False
        # Find the switch which has left
        for addedSwitchInfo in self.m_graph['switches']:

            findFlag = False
            for switch in all_switch_info:

                # Match dpid's
                if addedSwitchInfo.id == switch.dp.id:
                    findFlag = True
                    break
            
            if findFlag == False:
                leftSwitch = addedSwitchInfo
                break

        # Sanity Check
        if findFlag == True:
            return

        # Remove Switch entries
        self.m_graph['switches'].remove(leftSwitch)
        dpid = leftSwitch.id
        if dpid in self.m_ovs_mac:
            del(self.m_ovs_mac[dpid])

        for other_dpid,linked_dpid in self.m_graph['edges'].items():
            for link,port in linked_dpid.items():
                if link == dpid:
                    self.m_graph['edges'][other_dpid].pop(link)
                    break
        
        if dpid in self.m_graph['edges']:
            self.m_graph['edges'].pop(dpid)
            LOG_DEBUG(self.m_graph['edges'])

        if dpid in self.m_graph['hosts']:
            self.m_graph['hosts'].pop(dpid)
            LOG_DEBUG(self.m_graph['hosts'])

        if dpid in self.m_dpid_to_mac_port:
            for key,value in self.m_dpid_to_mac_port[dpid].items():
                mac = key
                self.m_mac_to_dpid_port.pop(mac, None)

        if dpid in self.m_dpid_to_mac_port:
            self.m_dpid_to_mac_port.pop(dpid, None)
            LOG_DEBUG(self.m_dpid_to_mac_port)

        # Remove Switch-Latency Monitoring Entry
        if dpid in self.m_switchLatencyStats:
            del self.m_switchLatencyStats[dpid]

        # Remove Link-Latency Monitoring Entry
        if dpid in self.m_linkLatencyStats:
            del self.m_linkLatencyStats[dpid]

        # Remove Hypervisor Memory Stats
        if dpid in self.m_hypervisorMemStats:
            del self.m_hypervisorMemStats[dpid]

        # Remove Hypervisor CPU Utilization Stats
        if dpid in self.m_hypervisorCpuUtilStats:
            del self.m_hypervisorCpuUtilStats[dpid]

        # Remove Hypervisor VNF Status 
        if dpid in self.m_hypVNFStatus:
            del self.m_hypVNFStatus[dpid]

        # Update network's Spanning Tree
        for datapath in self.m_graph['switches']:
            self._calculate_SpanningTree(datapath.id)
            break

    # Host Add Event
    @set_ev_cls(event.EventHostAdd, MAIN_DISPATCHER)
    def update_topology_hostAdd(self, ev):

        # Host information
        mac  = ev.host.mac
        dpid = ev.host.port.dpid
        port = ev.host.port.port_no

        # Code commented for Testing with Mininet

        if "00:00:00:00:00" not in mac:
            return

        LOG_INFO("Host added @ dpid - %s : %s via port - %s" % (dpid, mac, port))

        # Sanity Check
        if dpid in self.m_graph['hosts'] and mac in self.m_graph['hosts'][dpid]:
            return

        # Maintain the Data-structures
        # m_graph['hosts'] [dpid] [mac] => port
        if mac not in self.m_graph['hosts'][dpid]:
            self.m_graph['hosts'][dpid].setdefault(mac,{})

        self.m_graph['hosts'][dpid][mac]=port

        # mac  -> (dpid,port)
        self.m_mac_to_dpid_port[mac] = make_tuple(dpid, port)

        # dpid -> (mac, port)
        if dpid not in self.m_dpid_to_mac_port:
            self.m_dpid_to_mac_port.setdefault(dpid, {})
        self.m_dpid_to_mac_port[dpid][mac] = port

        if False and LOGGING_DEBUG:
            LOG_DEBUG("Saved Host information : " + str(mac) + " : " + str(dpid) + " : " + str(port))

        # If VNF is a Migrated, context will be maintained
        if mac in self.m_vnfOperationsOnStart:

            # Check Host belongs to a Migrating SLA to Cloud
            newVNFId   = self.m_vnfOperationsOnStart[mac]['new_vnfId']
            newVNFInfo = gUsedVNFIds[newVNFId]

            # Complete rest of the VNF Migration actions
            if newVNFInfo.slaIdentifier in self.m_SLACloudOperationsOnStart:
                self.migrateToCloud_SLARestOp(newVNFInfo, self.m_SLACloudOperationsOnStart[newVNFInfo.slaIdentifier])

            # Complete rest of the VNF Migration actions
            else:
                self.migrateVNF_VNFRestOp(self.m_vnfOperationsOnStart[mac], dpid)

            del self.m_vnfOperationsOnStart[mac]

        # Update network's Spanning Tree
        #LOG_DEBUG("Event: Host Added @ %s : %s - Re-calcuting Spanning Tree" % (dpid,mac))


    # Link add event
    @set_ev_cls(event.EventLinkAdd)
    def update_topology_linkAdd(self, ev):
        link = ev.link
        # Switches inter-connections
        self.m_graph['edges'][link.src.dpid][link.dst.dpid] = int(link.src.port_no)
        self.m_graph['edges'][link.dst.dpid][link.src.dpid] = int(link.dst.port_no)

        if LOGGING_DEBUG:
            LOG_DEBUG("Saved Link Information: " + str(link.src.dpid) + " <-> " + str(link.dst.dpid))
            LOG_DEBUG("Event: Link Added - Re-calcuting Spanning Tree")

        # Update network's Spanning Tree used for Flooding purpose
        for datapath in self.m_graph['switches']:
            self._calculate_SpanningTree(datapath.id)
            break


    # Updates the controller's view of switches in network topology
    def _calculate_SpanningTree(self, src):
        self.m_spTreeLinks = {}
        queue = deque()
        color = {}

        for node in self.m_graph['switches']:
            self.m_spTreeLinks[node.id] = set()
            color[node.id] = COLOR_WHITE

        queue.append(src)

        while queue:
            u = queue.popleft()
            color[u] = COLOR_BLACK
            for v,port in self.m_graph['edges'][u].items():
                # TODO : Improve by using weights among the edges
                # Boils down to simple BFS
                if color[v] == COLOR_WHITE:
                    self.m_spTreeLinks[v].add(u)
                    self.m_spTreeLinks[u].add(v)
                    color[v] = COLOR_BLACK
                    queue.append(v)
        
        if LOGGING_DEBUG:
            LOG_DEBUG("Spanning Tree: " )
            for u in self.m_graph['switches']:
                LOG_DEBUG( str(u.id) + " <-> " + str(self.m_spTreeLinks[u.id]))

    # ---------------------------------------------
    # ORCHESTRATOR's MESSAGE HANDLERS
    # ---------------------------------------------

    # Handles messages from Flow Manager
    def _DO_handleFlowManagerMessage(self, message):
        return
        LOG_DEBUG("-------------------------------")
        LOG_DEBUG("Flow Manager says :")
        LOG_DEBUG(message)
        LOG_DEBUG("-------------------------------")


    # Handles messages from bottleneck Detector
    def _DO_handleDetectorMessage(self, message):
        LOG_DEBUG("-------------------------------")
        LOG_DEBUG("Detector says :")
        LOG_DEBUG(message)
        LOG_DEBUG("-------------------------------")


    # Handle messages from Operator API
    def _DO_handleOperatorMessage(self, message, sock):
        retMsg = ""

        # Commands
        msgPart = message.split()

        # List Information - Read-Only Operation
        if msgPart[0] == 'list':

            # Format - "list all"
            if len(msgPart) == 1 or msgPart[1] == "all":
                retMsg = "Every Switch, VNFs and their links\n"

                retMsg += "Switches: \n"
                for item in self.m_graph['switches']:
                    LOG_DEBUG("----")
                    LOG_DEBUG(item.id)
                    LOG_DEBUG("----")

                    retVal,anot_msg = self._getSwitchInfo(item.id)
                    LOG_DEBUG(str(retVal) + " : " + str(anot_msg))
                    if retVal == SUCCESS:
                        retMsg += anot_msg

                retMsg += "VNFs: \n"
                if self.m_dpid_to_vnf.items:
                    for key,val in self.m_dpid_to_vnf.items():
                        retMsg += str(key) + " : "
                        for item in val:
                            retMsg += str(item) + " "
                        retMsg += '\n'
                else:
                    retMsg += "No VNFs are currently installed\n"

            # Format - "list switches"
            elif msgPart[1] == "switches":
                retMsg = "All switch Information\n"

                for item in self.m_graph['switches']:
                    retVal,anot_msg = self._getSwitchInfo(item.id)
                    if retVal == SUCCESS:
                        retMsg += anot_msg


            # Format - "list <switch_name>"
            # ex. list s1
            # Shows all the links connected to this 'specific' switch and all VNFs connected to this.
            elif msgPart[1] == "switch":
                retMsg = "Switch specific information :\n"
                dpid = int(msgPart[2].lstrip('s'))

                retVal,retMsg = self._getSwitchInfo(dpid) # Retreive Switch Info

                if retVal == SUCCESS:
                    retVal,anot_msg = self._getLinkedVNF(dpid) # Retreive Linked VNFs
                    retMsg = retMsg + anot_msg if retVal == SUCCESS else anot_msg

            # Format - "list nfvs"
            # Shows all NFVs with whom they are connected
            elif msgPart[1] == "vnfs":
                retMsg = ""
                
                if self.m_dpid_to_vnf:
                    retMsg = "All NFVs installed\n"
                    for key,val in self.m_dpid_to_vnf.items():
                        retMsg += str(key)
                        for item in val:
                            retMsg += str(item) + " "
                        retMsg += '\n'
                else:
                    retMsg += 'No VNFs are currently installed.\n'

            # Format - "list nfv <nfv_name>"
            # ex. list nfv f2
            elif msgPart[1] == "vnf" and msgPart[2] is not None:
                retMsg = ""

                vNFid = msgPart[2].lstrip('f')
                
                # Retreive VNF Info
                retVal,anot_msg = self._getVNFInfo(vNFid)
                retMsg = "NFV specific information\n" + anot_msg if retVal == SUCCESS else anot_msg

            else:
                retMsg = "Invalid List Command\n"
                retMsg += "List arguments:\n"
                retMsg += "List all information - list all\n"
                retMsg += "List all switches - list switches\n"
                retMsg += "List specific switch - list switch <switch_name>\n"
                retMsg += "List all VNFs - list vnf\n"
                retMsg += "List specific VNF - list vnf <vnf_name>\n"

        elif msgPart[0] == 'add':

            if len(msgPart) == 3:
                # Format - "add <switch_name> <nfv_name>"
                # ex. add s1 f2
                # Adds a VNF with a specific Switch
                retMsg = "VNF added\n"

            else:
                retMsg = "Invalid Command\n"
                retMsg += "add <switch_name> <nfv_name>\n"

        # Reply to Operator
        sock.send(retMsg)

    # ------------------------
    # Sub-Functions
    # ------------------------
    
    def _getSwitchInfo(self, dpid):
        retMsg = "Switch s%s -\n" % dpid
        checkSwitch = False

        # Validate Switch
        for switch in self.m_graph['switches']:
            if switch.id == dpid:
                checkSwitch = True

        # Get Linked VNF
        if checkSwitch:
            retVal,anot_msg = self._getLinkedVNF(dpid)
            if retVal != SUCCESS:
                return retVal,anot_msg
            else:
                retMsg += "VNFs: " + anot_msg
        else:
            return FAILURE,"Switch not found.\n"
        
        # Get Linked Nbrs
        retMsg += "Nbrs: "
        retVal, anot_msg = self._getSwitchNbrs(dpid)
        return (SUCCESS,retMsg + anot_msg) if retVal == SUCCESS else (retVal,anot_msg)
        
    # Returns all VNFs linked to the Switch
    def _getLinkedVNF(self, dpid):
        retMsg = ""

        if self.m_dpid_to_vnf and dpid in self.m_dpid_to_vnf:
            for item in self.m_dpid_to_vnf[dpid]:
                retMsg += str(item) + " "

            retMsg += '\n'
            return SUCCESS,retMsg
        
        else:
            return SUCCESS,"No VNF attached to this Switch\n"

    # Returns Switch Connected to the VNF
    def _getVNFInfo(self, vNFid):

        if self.m_dpid_to_vnf:
            for key,value in self.m_dpid_to_vnf.items():
                if value == vNFid:
                    return SUCCESS, "Connected to: s%s\n" % key
        
        return FAILURE, "VNF not found.\n"

    # Returns all neighbours of the Switch
    def _getSwitchNbrs(self, dpid):
        retMsg = ""

        if dpid in self.m_graph['edges']:
            for item in self.m_graph['edges'][dpid]:
                retMsg += "s" + str(item).lstrip('0') + " "
            
            retMsg += '\n'
            return SUCCESS,retMsg

        else:
            return FAILURE, "Switch Not found\n"


    # -----------------------------------------
    # Orchestor's Operator Thread - using Sockets
    # -----------------------------------------
    def DO_openSocketThreadAPI(self):
        try:
            # Create the Orchestrator Thread
            self.socket_thread = hub.spawn(self._DO_operatorSocket)
        except:
            LOG_DEBUG("Error: unable to start Orchestrator thread")

    def _DO_operatorSocket(self):

        connectionList = []
        server_socket = socket.socket()         # Create a socket object
        host = IP_ADDR                          # Get local machine name
        port = OPERATOR_API_SOCK_PORT           # Reserve a port for your service.
        server_socket.bind((host, port))        # Bind to the port

        server_socket.listen(5)                 # Now wait for client connection.

        # Add server socket to the list of readable connections
        connectionList.append(server_socket)

        while True:

            read_sockets,write_sockets,error_sockets = select.select(connectionList,[],[])

            for sock in read_sockets:

                # New connection
                if sock == server_socket:

                    sockfd, addr = server_socket.accept()
                    connectionList.append(sockfd)
                    LOG_DEBUG("Operator (%s) connected" % addr)
                    print "Operator (%s) connected" % addr

                # Incoming message from Operator API
                else:
                    # Data recieved
                    try:
                        message = sock.recv(RECV_BUFFER)
                        if message:
                            # Handle Operator Message
                            # Push Message into Orchestrator Queue
                            customMsg = {}
                            customMsg['type'] = "Operator"
                            customMsg['message'] = message
                            customMsg['socket'] = sock

                            self.orchestratorMsgQueue.put(customMsg)

                            LOG_DEBUG("Recvd Message: %s" % customMsg)
                    except:
                        sock.close()
                        connectionList.remove(sock)
                        continue

        server_socket.close()


    # -----------------------------------------
    # SLA's related Functions
    # -----------------------------------------

    # Maps EndUsers to SLA aggrements
    def mapEndUsersToSLAs(self, sla_object):

        for end_user in sla_object.endUsersMac:
            # Initialize
            if end_user not in self.m_end_users_to_SLA:
                self.m_end_users_to_SLA[end_user] = []

            # The Endpoint may belong to many SLA's
            self.m_end_users_to_SLA[end_user].append(sla_object.identifier)

            # Allocate VNF ID
            vnfID = int(end_user.split(":")[5])
            if gUsedVNFIds[vnfID] == False: # Empty Slot
                gUsedVNFIds[vnfID] = True   # Used by Host

    # Check wether end-users belong to an SLA
    def checkEndUsersToSLA(self, endUser1, endUser2):

        # End-users may belong to many SLAs
        result = []

        if endUser1 in self.m_end_users_to_SLA:

            for sla_id in self.m_end_users_to_SLA[endUser1]:

                sla_object = self.m_SLAs[sla_id]
                
                # Both endpoints belong to the same SLA
                if endUser2 in sla_object.endUsersMac:
                    result.append(sla_object)

        return result

    # -----------------------------------------
    # Bottleneck Removal related Functions
    # -----------------------------------------

    # Creates Priority Score of moving VNF to Nbr Hypervisor
    def generatePriorityScore(self, vnfInfo, dpid, nbr_dpid):

        # Get linked SLA
        sla = self.m_SLAs[vnfInfo.slaIdentifier]
        delayBuffer = sla.delayBuffer

        #pdb.set_trace()

        #### Parameter - 1: Link Latency between Current and Nbr
        if dpid > nbr_dpid:
            linkLatency = self.m_linkLatencyStats[dpid][nbr_dpid]['data']
        else:
            linkLatency = self.m_linkLatencyStats[nbr_dpid][dpid]['data']

        # TODO: Improve based on the existing Path of the Service Chain
        # Case 1 : Along the path of the Service Chain

        # Case 2 : Addition in the path


        #### Parameter - 2: VNF's CPU Mem Requirement
        cpuMemReq    = vnfInfo.cpuMemReq
        cpuMemUnused = self.m_hypervisorMemStats[nbr_dpid]['capacity'] - self.m_hypervisorMemStats[nbr_dpid]['used']

        if cpuMemReq > cpuMemUnused:
            return [], FAILURE

        # CPU Mem Remaining after Moving the VNF to the Nbr
        paramCpuMemRemain = cpuMemUnused - cpuMemReq

        #### Parameter - 3: Link Bandwidth between Current and Nbr
        if dpid > nbr_dpid:
            curr_to_nbrPort   = self.m_graph['edges'][dpid][nbr_dpid]
            linkBandwidthUsed = self.m_switchFlowStats[dpid][curr_to_nbrPort]['data'][1]
        else:
            curr_to_nbrPort       = self.m_graph['edges'][nbr_dpid][dpid]
            linkBandwidthUsed = self.m_switchFlowStats[nbr_dpid][curr_to_nbrPort]['data'][1]


        linkBandwidthReq         = sla.reqBW
        # TODO : Link capacity for each link is different
        #paramLinkBandwidthUnused = self.m_switchFlowStats[dpid][curr_to_nbrPort]['capacity'] - linkBandwidthUsed

        paramLinkBandwidthUnused = LINK_BW_LIMIT - linkBandwidthUsed

        if linkBandwidthReq > paramLinkBandwidthUnused:
            return [], FAILURE

        # ppscore
        priorityScore = (alpha * paramCpuMemRemain) + (beta * paramLinkBandwidthUnused) - (gamma * linkLatency)

        return priorityScore,SUCCESS

    # Updates new SLA Flow Rules
    def updateNewSLAFlowRules(self, sla, isForAllPairs, in_src_mac, in_dst_mac):

        #pdb.set_trace()

        if isForAllPairs:
            srcUsersMac = sla.endUsersMac
            dstUsersMac = sla.endUsersMac
        else:
            srcUsersMac = [in_src_mac]
            dstUsersMac = [in_dst_mac]

        for src_mac in srcUsersMac:
            for dst_mac in dstUsersMac:
                if src_mac == dst_mac:
                    continue

                # Sanity Check
                if src_mac not in sla.compPathOfSLA and dst_mac not in sla.compPathOfSLA[src_mac]:
                    LOG_ERROR("This scenario should not occur. Programming Error!!!")
                    continue

                # Installation of the respective flow Rules will be done here
                    
                priority = sla.compPathOfSLA[src_mac][dst_mac]['priority']
                path     = sla.compPathOfSLA[src_mac][dst_mac]['currPath']

                # Add New Flows for the Current Path
                
                processed_vnf_cnt = 0

                src_dpid    = self.m_mac_to_dpid_port[src_mac].val1
                dst_dpid    = self.m_mac_to_dpid_port[dst_mac].val1
                src_in_port = self.m_mac_to_dpid_port[src_mac].val2

                ## 1. Actor - Ingress Switch via In-between Switches
                prev_switch = src_dpid
                slaIndex = 1

                while slaIndex < len(path):

                    # Pair contains [dpid, Information]
                    # Information : {-1 : End Point, 0 : Intermediate Switch, <Num> : No. of VNFs isntalled}
                    pair = path[slaIndex]

                    # Reached the Switch with the First VNF installed
                    if pair[1] != 0:
                        break

                    this_dpid   = pair[0]
                    datapath    = self.getDatapath(this_dpid)
                    parser      = datapath.ofproto_parser
                    ofproto     = datapath.ofproto
                    next_switch = path[slaIndex + 1][0]

                    # TODO : Assuming Hosts connected to the Hypervisor's
                    in_port     = self.m_graph['edges'][this_dpid][prev_switch] if this_dpid != prev_switch else src_in_port
                    out_port    = ofproto.OFPP_IN_PORT if this_dpid == next_switch else self.m_graph['edges'][this_dpid][next_switch]

                    match       = parser.OFPMatch(vlan_vid=(sla.vlanCommonTag | processed_vnf_cnt), in_port=in_port, eth_src=src_mac, eth_dst=dst_mac)
                    actions     = [parser.OFPActionOutput(out_port)]
                    self.add_flow(datapath, priority, match, actions)
                    LOG_DEVEL("Datapath: %s | Match : vlan_tag-%s in_port-%s eth_src-%s eth_dst-%s | Output : out_port-%s" % (this_dpid, sla.vlanCommonTag | processed_vnf_cnt, in_port, src_mac, dst_mac, out_port))

                    prev_switch = this_dpid
                    slaIndex   += 1

                ## 2. Actor - All the VNFs of the Service Chain
                ## Packet starts processing from 1st VNF to the rest of the VNF(s), if any
                prev_in_port = src_in_port

                # Check and count whether multiple VNF(s) are connected to the same Hypervisor
                isMultipleVNFsAtSameDpid = path[slaIndex][1] - 1

                while True:

                    this_dpid    = path[slaIndex][0]
                    datapath     = self.getDatapath(this_dpid)
                    parser       = datapath.ofproto_parser
                    ofproto      = datapath.ofproto
                    in_port      = self.m_graph['edges'][this_dpid][prev_switch] if this_dpid != prev_switch else prev_in_port
                    prev_in_port = in_port

                    next_switch  = path[slaIndex][0] if isMultipleVNFsAtSameDpid > 0 else path[slaIndex + 1][0]
                    out_port     = ofproto.OFPP_IN_PORT if this_dpid == next_switch else self.m_graph['edges'][this_dpid][next_switch]

                    # VNF installed over this dpid
                    if path[slaIndex][1] != 0:

                        # Change dst_Mac to mac_address of the VNF
                        vnf_mac      = sla.VNFsNetworkMac[processed_vnf_cnt]
                        vnf_out_port = self.m_mac_to_dpid_port[vnf_mac].val2
                        vnf_out_port = ofproto.OFPP_IN_PORT if vnf_out_port == in_port else vnf_out_port
                    
                        # If multiple VNFs at same Hypervisor
                        if isMultipleVNFsAtSameDpid:
                            # Do nothing, Packet sent in previous iteration
                            LOG_DEVEL("Handling Multiple Consecutive VNFs at the Same Hypervisor %s" % this_dpid)

                        # Receiving Packet for first time
                        elif this_dpid == prev_switch:
                            match   = parser.OFPMatch(in_port=in_port, eth_src=src_mac, eth_dst=dst_mac)
                            actions = [parser.OFPActionSetField(eth_src=self.m_ovs_mac[this_dpid]),
                                       parser.OFPActionSetField(eth_dst=vnf_mac),
                                       parser.OFPActionOutput(vnf_out_port)]

                            self.add_flow(datapath, priority, match, actions)
                            LOG_DEVEL("Datapath: %s | Match : in_port-%s eth_src-%s eth_dst-%s | SetFeild : eth_dst - %s, Output : out_port-%s" % (this_dpid, in_port, src_mac, dst_mac, vnf_mac, vnf_out_port))

                        else:
                            # Check VLAN Tag
                            match   = parser.OFPMatch(vlan_vid=(sla.vlanCommonTag | processed_vnf_cnt),in_port=in_port,eth_src=src_mac,eth_dst=dst_mac)
                            actions = [parser.OFPActionPopVlan(0x8100),
                                       parser.OFPActionSetField(eth_src=self.m_ovs_mac[this_dpid]),
                                       parser.OFPActionSetField(eth_dst=vnf_mac),
                                       parser.OFPActionOutput(vnf_out_port)]

                            self.add_flow(datapath, priority, match, actions)
                            LOG_DEVEL("Datapath: %s | Match : vlan_vid-%s in_port-%s eth_src-%s eth_dst-%s | SetFeild : eth_src - %s, eth_dst - %s, Output : out_port-%s" % (this_dpid, sla.vlanCommonTag | processed_vnf_cnt, in_port, src_mac, dst_mac, self.m_ovs_mac[this_dpid], vnf_mac, vnf_out_port))
                       
                        processed_vnf_cnt += 1
                        prev_switch = this_dpid

                        # Packet receiving from Last VNF
                        # Scenario Handled in next Section.
                        # All VNF(s) have been processed
                        if processed_vnf_cnt == len(sla.VNFsNetworkDpid):
                            break

                        # Re-direct the packet received from the VNF through the Service Chain/Destination
                        match = parser.OFPMatch(in_port=vnf_out_port, eth_src=vnf_mac, eth_dst=dst_mac)

                        # Next VNF at the same Hypervisor
                        if this_dpid == next_switch:
                            out_port     = ofproto.OFPP_IN_PORT
                            next_vnf_mac = sla.VNFsNetworkMac[processed_vnf_cnt]
                            actions      = [parser.OFPActionSetField(eth_src=src_mac),
                                            parser.OFPActionSetField(eth_dst=next_vnf_mac),
                                            parser.OFPActionOutput(out_port)]

                            LOG_DEVEL("Datapath: %s | Match : in_port-%s eth_src-%s eth_dst-%s | SetFeild : eth_src - %s, eth_dst-%s Output : out_port-%s" % (this_dpid, vnf_out_port, vnf_mac, dst_mac, src_mac, next_vnf_mac, out_port))

                        else:
                            # Add VLAN Tag for processing in next Switch(s)
                            out_port = self.m_graph['edges'][this_dpid][next_switch]
                            actions  = [parser.OFPActionPushVlan(0x8100),
                                        parser.OFPActionSetField(vlan_vid=(sla.vlanCommonTag | processed_vnf_cnt)),
                                        parser.OFPActionSetField(eth_src=src_mac),
                                        parser.OFPActionOutput(out_port)]

                            LOG_DEVEL("Datapath: %s | Match : in_port-%s eth_src-%s eth_dst-%s | SetFeild : vlan_tag-%s, eth_src - %s, Output : out_port-%s" % (this_dpid, vnf_out_port, vnf_mac, dst_mac, sla.vlanCommonTag | processed_vnf_cnt, src_mac, out_port))

                        self.add_flow(datapath, priority, match, actions)

                    # Intermediate Switches
                    else:
                        match   = parser.OFPMatch(vlan_vid=(sla.vlanCommonTag | processed_vnf_cnt),in_port=in_port,eth_src=src_mac,eth_dst=dst_mac)
                        actions = [parser.OFPActionOutput(out_port)]
                        self.add_flow(datapath, priority, match, actions)
                        LOG_DEVEL("Datapath: %s | Match : vlan_tag-%s in_port-%s eth_src-%s eth_dst-%s | Output : out_port-%s" % (this_dpid, sla.vlanCommonTag | processed_vnf_cnt, in_port, src_mac, dst_mac, out_port))

                        prev_switch = this_dpid

                    if isMultipleVNFsAtSameDpid == 0:
                        slaIndex += 1
                    else:
                        isMultipleVNFsAtSameDpid -= 1

                ## 3. Actor - Last VNF and Intermediate Switches
                # Re-direct the packet from Last VNF to the Egress Point (Actual Dest. Point)
                last_vnf_mac  = sla.VNFsNetworkMac[-1]
                last_vnf_dpid = sla.VNFsNetworkDpid[-1]

                ## Case 3a. Destination VNF Hypervisor is also connected to the Egress Switch
                if prev_switch == dst_dpid:

                    # Re-direct the packet from the VNF towards the destination
                    datapath  = self.getDatapath(dst_dpid)
                    parser    = datapath.ofproto_parser
                    ofproto   = datapath.ofproto
                    same_port = self.m_mac_to_dpid_port[dst_mac].val1
                    match     = parser.OFPMatch(in_port=same_port,eth_src=last_vnf_mac,eth_dst=dst_mac)
                    actions   = [parser.OFPActionSetField(eth_src=src_mac),
                                 parser.OFPActionOutput(ofproto.OFPP_IN_PORT)]
                    self.add_flow(datapath, priority, match, actions)
                    LOG_DEVEL("Datapath: %s | Match : in_port-%s eth_src-%s eth_dst-%s | SetFeild : eth_src - %s, Output : out_port-%s" % (dst_dpid, same_port, last_vnf_mac, dst_mac, src_mac, ofproto.OFPP_IN_PORT))

                ## Case 3b. Last VNF Hypervisor and Egress Switch are not same
                else:
                    last_vnf_in_port = self.m_dpid_to_mac_port[last_vnf_dpid][last_vnf_mac]

                    while path[slaIndex][1] != -1:

                        #pdb.set_trace()
                        this_dpid   = path[slaIndex][0]
                        datapath    = self.getDatapath(this_dpid)
                        parser      = datapath.ofproto_parser
                        ofproto     = datapath.ofproto
                        next_switch = path[slaIndex + 1][0]
                        in_port     = last_vnf_in_port if slaIndex == 0 or this_dpid == prev_switch else self.m_graph['edges'][this_dpid][prev_switch]
                        out_port    = self.m_graph['edges'][this_dpid][next_switch]
                        out_port    = ofproto.OFPP_IN_PORT if out_port == in_port else out_port

                        # Re-format the packet from the Last VNF towards the actual destination
                        if this_dpid == last_vnf_dpid:
                            match   = parser.OFPMatch(in_port=in_port, eth_src=last_vnf_mac, eth_dst=dst_mac)
                            # Add VLAN Tag for processing in the last Switch
                            actions = [parser.OFPActionPushVlan(0x8100),
                                       parser.OFPActionSetField(vlan_vid=(sla.vlanCommonTag | processed_vnf_cnt)),
                                       parser.OFPActionSetField(eth_src=src_mac),
                                       parser.OFPActionOutput(out_port)]
                            self.add_flow(datapath, priority, match, actions)
                            LOG_DEVEL("Datapath: %s | Match : in_port-%s eth_src-%s eth_dst-%s | SetFeild : vlan_tag-%s eth_src - %s, Output : out_port-%s" % (this_dpid, in_port, last_vnf_mac, dst_mac, sla.vlanCommonTag | processed_vnf_cnt, src_mac, out_port))

                        # Intermediate Switches
                        else:
                            match    = parser.OFPMatch(vlan_vid=(sla.vlanCommonTag | processed_vnf_cnt), in_port=in_port, eth_src=src_mac, eth_dst=dst_mac)
                            actions  = [parser.OFPActionOutput(out_port)]
                            self.add_flow(datapath, priority, match, actions)
                            LOG_DEVEL("Datapath: %s | Match : vlan_tag-%s in_port-%s eth_src-%s eth_dst-%s | Output : out_port-%s" % (this_dpid, sla.vlanCommonTag | processed_vnf_cnt, in_port, src_mac, dst_mac, out_port))

                        prev_switch = this_dpid
                        slaIndex   += 1

                ## Case 4. Actor - Egress Switch
                if prev_switch != dst_dpid:
                    datapath = self.getDatapath(dst_dpid)
                    parser   = datapath.ofproto_parser
                    ofproto  = datapath.ofproto
                    in_port  = self.m_graph['edges'][dst_dpid][prev_switch]
                    out_port = self.m_mac_to_dpid_port[dst_mac].val2
                    match    = parser.OFPMatch(vlan_vid=(sla.vlanCommonTag | processed_vnf_cnt), in_port=in_port, eth_dst=dst_mac)
                    actions  = [parser.OFPActionPopVlan(0x8100),
                                parser.OFPActionOutput(out_port)]
                    self.add_flow(datapath, priority, match, actions)
                    LOG_DEVEL("Datapath: %s | Match : vlan_tag-%s in_port-%s eth_dst-%s | Output : out_port-%s" % (dst_dpid, sla.vlanCommonTag | processed_vnf_cnt, in_port, dst_mac, out_port))


                ## 5. Actor - Ingress Switch
                # Case 5a. Ingrees Switch and Centre Switch are not same
                if len(path) > 2 and path[0][0] != path[1][0]:

                    datapath    = self.getDatapath(src_dpid)
                    parser      = datapath.ofproto_parser
                    ofproto     = datapath.ofproto
                    next_switch = path[1][0]
                    out_port    = self.m_graph['edges'][src_dpid][next_switch]
                    match       = parser.OFPMatch(in_port=src_in_port, eth_src=src_mac, eth_dst=dst_mac)
                    # Add VLAN Tag for processing in next Switch(s)
                    actions     = [parser.OFPActionPushVlan(0x8100),
                                   parser.OFPActionSetField(vlan_vid=sla.vlanCommonTag),
                                   parser.OFPActionOutput(out_port)]

                    if src_in_port == out_port:
                        return

                    self.add_flow(datapath, priority, match, actions) # Flow-Mod
                    LOG_DEVEL("Datapath: %s | Match : in_port-%s eth_src-%s eth_dst-%s | Output : vlan_vid-%s out_port-%s" % (src_dpid, src_in_port, src_mac, dst_mac, sla.vlanCommonTag, out_port))

    # Merges Duplicate consecutive entries from the input List
    # e.g. Input  - [[2 1] [3 2] [3 1] [5 3]]
    #      Output - [[2 1] [3 3] [5 3]]
    def mergeDuplicateEntries(self, inputList):

        isUpdateInLastIteration = True
        inList     = copy.deepcopy(inputList)
        outList    = []

        # Iterated until there are no matches
        while isUpdateInLastIteration:

            isUpdateInLastIteration = False

            outList = []
            outListLen = 0

            for index in range(0, len(inList)):
                # Merge Element
                if inList[index][1] != -1 and outList[outListLen-1][1] != -1 and outList[outListLen-1][0] == inList[index][0]:

                    outList[outListLen-1][1] += inList[index][1]
                    isUpdateInLastIteration = True

                # New Element
                else:
                    outList.append(inList[index])
                    outListLen += 1

            inList = copy.deepcopy(outList)

        return outList


    # Updates the Complete Path of SLA for all pairs of Hosts in the SLA
    def updateCompPathOfSLA(self, sla, vnfId, nbr_dpid):

        vnfInfo = gUsedVNFIds[vnfId]

        for src_mac in sla.endUsersMac:
            for dst_mac in sla.endUsersMac:

                # Sanity Check
                if src_mac == dst_mac:
                    continue

                sla.compPathOfSLA[src_mac][dst_mac]['prevPath'] = copy.deepcopy(sla.compPathOfSLA[src_mac][dst_mac]['currPath'])
                path = copy.deepcopy(sla.compPathOfSLA[src_mac][dst_mac]['currPath'])

                sla.compPathOfSLA[src_mac][dst_mac]['priority'] += 1

                vnfCount = 0
                for index in range(0, len(path)):

                    # Note the dpid(s) with the VNF
                    if path[index][1] != -1 and path[index][1] != 0:
                        vnfCount += 1
                        
                        # Index starts from '0'
                        if vnfCount == vnfInfo.servChainIndex + 1:

                            path[index][1] -= 1

                            prev_nbr_dpid = path[index + 1][0]
                            path.insert(index + 1, [nbr_dpid, 1])

                            # Three or more VNFs were installed
                            # e.g.  Input: [[2 4]]
                            #      Output: [[2 1] [nbr_dpid 1] [2 2]]
                            if path[index][1] > 0:
                                
                                count = path[index][1] - 1
                                path[index][1] = 1

                                path.insert(index + 2, [path[index][0], count])
                                prev_nbr_dpid = path[index][0]

                            index += 1

                            # Retreive Path between the two switches
                            intermPath = self.getSrcToDestPath(nbr_dpid, prev_nbr_dpid)

                            if len(intermPath) > 2:
                                # First and Last elements are Src and Dst Dpids, do not consider
                                del intermPath[-1]
                                del intermPath[0]

                                for dpid in reversed(intermPath):
                                    path.insert(index+1, [dpid, 0])

                            # Relax, and merging with Previous Dpid
                            # e.g. Input : [[1,1] [2,0] [3,0] [1,1]]
                            #     Output : [[1,2]]
                            tempIndex = index - 1
                            while tempIndex != 0 and path[tempIndex][1] == 0 and path[tempIndex][0] != path[index][0]:
                                tempIndex -= 1

                            # Same dpid having intermediate switches
                            if tempIndex != 0 and path[tempIndex][0] == path[index][0]:
                                path[index][1] += path[tempIndex][1]
                                del path[tempIndex : index]

                            elif tempIndex == 0 and path[tempIndex][0] == path[index][0]:
                                del path[1 : index]

                            # Club duplicate entries, if exists
                            path = self.mergeDuplicateEntries(path)
    
                            sla.compPathOfSLA[src_mac][dst_mac]['currPath'] = copy.deepcopy(path)

                            LOG_DEBUG("For Hosts %s -> %s: " % (src_mac, dst_mac))
                            LOG_DEBUG("Previous Path: %s" % sla.compPathOfSLA[src_mac][dst_mac]['prevPath'])
                            LOG_DEBUG("Current  Path: %s" % sla.compPathOfSLA[src_mac][dst_mac]['currPath'])

                            break

    # Handles migration of VNF from Current Hypervisor to Nbr Hypervisor
    # Scope : Completes all other operations for Migration
    def migrateVNF_VNFRestOp(self, savedContext, new_dpid):

        old_dpid  = savedContext['old_dpid']
        old_mac   = savedContext['old_mac']
        old_vnfId = savedContext['old_vnfId']
        new_vnfId = savedContext['new_vnfId']

        oldVNFInfo  = gUsedVNFIds[old_vnfId]
        newVNFInfo  = gUsedVNFIds[new_vnfId]
        
        vnfIndexOfServiceChain = newVNFInfo.servChainIndex
        sla = self.m_SLAs[oldVNFInfo.slaIdentifier]

        # Update Complete Path of SLA
        self.updateCompPathOfSLA(sla, new_vnfId, new_dpid)

        # Maintain old information for Removing Flow Rules
        oldVNFsNetworkDpid = copy.deepcopy(sla.VNFsNetworkDpid)
        oldVNFsNetworkMac  = copy.deepcopy(sla.VNFsNetworkMac)
        oldVNFsNetworkMac[vnfIndexOfServiceChain] = old_mac

        ## Step 3: Update VNF Information w.r.t. New Dpid in all related data-structures
        sla.VNFsNetworkDpid[vnfIndexOfServiceChain] = new_dpid
        newVNFInfo.dpid                             = new_dpid

        # Map VNFInfo to New Hypervisor
        self.m_hypVNFStatus[newVNFInfo.dpid].append(newVNFInfo.identifier)
        self.m_hypervisorMemStats[new_dpid]['used'] += newVNFInfo.cpuMemReq
        self.m_hypervisorMemStats[old_dpid]['used'] -= newVNFInfo.cpuMemReq

        ## Step 4 : Add New flow rules for this change with Higher Priority
        self.updateNewSLAFlowRules(sla, True, [], [])
        LOG_DEBUG("Installed New SLA Flow Rules for the SLA: %s" % sla.identifier)

        ## Step 5: Stop VNF at the current Hypervisor
        # Retrieve Old Hypervisor IP and sockfd
        hypIPAddr = self.m_dpid_to_hyp_ip[old_dpid]
        oldSockfd = ""

        for pair in self.m_hyp_ip_sockfd_pair:
            if hypIPAddr == pair.val1[0]:
                oldSockfd = pair.val2
                break

        # Sanity Check
        if oldSockfd == "":
            LOG_DEBUG("System communication with Old Hypervisor(%s) is broken. Migration Failed." % (new_dpid.dpid))
            return FAILURE

        # Stops VNF at the Old Hypervisor
        self.sendStopVNFCommand(oldVNFInfo, oldSockfd)

        ## Step 6: Remove Previous Flow Rules for all paths
        for src_mac in sla.endUsersMac:
            for dst_mac in sla.endUsersMac:

                # Sanity Check
                if src_mac == dst_mac:
                        continue

                if sla.compPathOfSLA[src_mac][dst_mac]['prevPath'] != []:

                    self.removeOldSLAFlowRules(sla, src_mac, dst_mac, sla.compPathOfSLA[src_mac][dst_mac]['prevPath'], oldVNFsNetworkDpid, oldVNFsNetworkMac)
                    sla.compPathOfSLA[src_mac][dst_mac]['prevPath'] = []

        ## Step 7: Update VNF Information w.r.t. Old Dpid in all related data-structures
        del self.m_mac_to_dpid_port[oldVNFInfo.macAddr]
        del self.m_dpid_to_mac_port[old_dpid][oldVNFInfo.macAddr]
        self.m_hypVNFStatus[old_dpid].remove(oldVNFInfo.identifier)

        LOG_INFO("Successful Migration in SLA (%s) of Old VNF(%s) from Hypervisor(%s) as New VNF(%s) at Hypervisor(%s)" % 
                  (sla.identifier, oldVNFInfo.identifier, old_dpid, newVNFInfo.identifier, new_dpid))

        # TODO: Step 7: Update Delay Buffer for the SLA


    # Updates the Complete Path of SLA for all pairs of Hosts w.r.t. Cloud
    def updateCompPathOfSLAInCloud(self, sla):

        for src_mac in sla.endUsersMac:
            for dst_mac in sla.endUsersMac:

                # Sanity Check
                if src_mac == dst_mac:
                    continue

                sla.compPathOfSLA[src_mac][dst_mac]['prevPath'] = copy.deepcopy(sla.compPathOfSLA[src_mac][dst_mac]['currPath'])
                path = sla.compPathOfSLA[src_mac][dst_mac]['currPath']

                new_path = []

                # Source Dpid
                new_path.append(path[0]) 
                pdb.set_trace()
                                             
                # Path from Source to Cloud
                src_to_cloud = self.getSrcToDestPath(path[0], CLOUD_DPID)                
                for dpid in range(1, len(src_to_cloud) - 1):
                    new_path.append([dpid, 0])

                # Service Chain
                new_path.append([CLOUD_DPID, len(sla.vnfInputList)])  

                # Path from Cloud to Destination
                dst_to_cloud = self.getSrcToDestPath(CLOUD_DPID, path[-1])
                for dpid in range(1, len(dst_to_cloud) - 1):
                    new_path.append([dpid, 0])
                
                # Dst Dpid
                new_path.append(path[-1])

                sla.compPathOfSLA[src_mac][dst_mac]['currPath'] = copy.deepcopy(new_path)

                LOG_DEBUG("For Hosts %s -> %s: " % (src_mac, dst_mac))
                LOG_DEBUG("Previous Path: %s" % sla.compPathOfSLA[src_mac][dst_mac]['prevPath'])
                LOG_DEBUG("Current  Path: %s" % sla.compPathOfSLA[src_mac][dst_mac]['currPath'])

    
    # Handles migration of VNF from Current Hypervisor to Nbr Hypervisor
    # Scope limited to Updating Complete Paths and starting VNF at Nbr Hypervisor
    def migrateVNF_VNFStartOp(self, dpid, new_dpid, vnfId):

        oldVNFInfo = gUsedVNFIds[vnfId]

        vnfIndexOfServiceChain = oldVNFInfo.servChainIndex
        sla = self.m_SLAs[oldVNFInfo.slaIdentifier]

        newVNFInfo = self.assignVNFResources(sla, oldVNFInfo.servChainIndex, dpid, True)

        old_dpid = sla.VNFsNetworkDpid[vnfIndexOfServiceChain]

        # Retrieve New Hypervisor IP and sockfd
        hypIPAddr = self.m_dpid_to_hyp_ip[new_dpid]
        newSockfd = ""

        for pair in self.m_hyp_ip_sockfd_pair:
            if hypIPAddr == pair.val1[0]:
                newSockfd = pair.val2
                break

        # Sanity Check
        if newSockfd == "":
            LOG_DEBUG("Incorrect Migration at Hypervisor (%s) or System communication with Hypervisor(%s) is broken." % (new_dpid.dpid, new_dpid.dpid))
            return FAILURE

        # Rest of the Actions to be taken after VNF comes up at the New Hypervisor
        # Ref: migrateVNF_VNFRestOp

        ## Step 1 :  Save current context

        # Sanity Check
        if newVNFInfo.macAddr in self.m_vnfOperationsOnStart:
            LOG_ERROR("This scenario should not occur. Highly impossible!!!")
            return

        self.m_vnfOperationsOnStart[newVNFInfo.macAddr]              = {}
        self.m_vnfOperationsOnStart[newVNFInfo.macAddr]['old_dpid']  = old_dpid
        self.m_vnfOperationsOnStart[newVNFInfo.macAddr]['old_mac']   = oldVNFInfo.macAddr
        self.m_vnfOperationsOnStart[newVNFInfo.macAddr]['old_vnfId'] = oldVNFInfo.identifier
        self.m_vnfOperationsOnStart[newVNFInfo.macAddr]['new_vnfId'] = newVNFInfo.identifier

        ## Step 2a : Start VNF at the Nbr Hypervisor with same configuration
        # Starts VNF at the Hypervisor
        self.sendStartVNFCommand(newVNFInfo, newSockfd)

        ## Step 2b : Forwarding Msg Command
        self.sendForwardingVNFCommand(sla, newVNFInfo, newSockfd, newVNFInfo.servChainIndex)

        '''
        # Check for last VNF
        if newVNFInfo.servChainIndex != len(sla.vnfInputList) - 1:
            # Retreive info of Next VNF in the Service Chain
            nextVNFDpid = sla.VNFsNetworkDpid[newVNFInfo.servChainIndex + 1]
            nextVNFMac  = sla.VNFsNetworkMac[newVNFInfo.servChainIndex + 1]
    
            nextVNFInfo = []
            for tempVNFId in self.m_hypVNFStatus[nextVNFDpid]:
                tempNextVNFInfo = gUsedVNFIds[tempVNFId]
                if nextVNFMac == tempNextVNFInfo.macAddr:
                    nextVNFInfo = tempNextVNFInfo
                    break

            # Sanity Check
            if nextVNFInfo == []:
                LOG_ERROR("This scenario should not occur. Programming Error!!!")
                return

            # Forward to Next VNF in the Service Chain
            

        else:
            # Forward from Last VNF to Destination Host
            self.sendForwardingVNFCommand(newVNFInfo, sockfd)
        '''

    # Handle Node Bottleneck
    def handleNodeBottleneck(self, dpid):
        priorityScores = {}

        # All VNFs installed at the Bottlenecked Hypervisor
        for vnfIndex in self.m_hypVNFStatus[dpid]:
            vnfInfo = gUsedVNFIds[vnfIndex]
            #LOG_INFO("Hypervisor (%s) : VNF (c%s) considered for Migration Algorithm (Case 1)." % (dpid, vnfInfo.identifier))

            # Consider all Nbrs of this dpid
            # Retrieve Nbrs of the current Dpid
            for nbr_dpid,out_port in self.m_graph['edges'][dpid].items():

                score,result = self.generatePriorityScore(vnfInfo, dpid, nbr_dpid)

                if result == SUCCESS:
                    priorityScores[make_tuple(vnfIndex, nbr_dpid)] = score

            maxPriorityScore = 0.0
            maxPSPair = []
            for pair in priorityScores:
                LOG_DEVEL("Moving VNF (c%s) from Current (%s) to Nbr (%s) Hypervisor : %s." % (vnfInfo.identifier, dpid, pair.val2, priorityScores[pair]))
    
                # TODO: BCase
                if priorityScores[pair] > maxPriorityScore: # and pair.val2 == 2:
                #if priorityScores[pair] > maxPriorityScore:
                    maxPriorityScore = priorityScores[pair]
                    maxPSPair = pair
            
            # Movement to the Nbrs not possible, leads to Case 2
            # TODO : 3case
            if maxPriorityScore == 0.0:
                #LOG_ERROR("This scenario should not occur (NOW). Programming Error!!!")
                self.handleNodeBottleneckCase3(dpid)
                return

            # Handles migration of VNF from Current Hypervisor to Nbr Hypervisor
            self.migrateVNF_VNFStartOp(dpid, maxPSPair.val2, maxPSPair.val1)


    # Handles migration of entire SLA (associated VNFs) to the Cloud
    # Scope limited to Updating Complete Paths and starting VNF at the Cloud
    def migrateToCloud_SLAStartOp(self, sla):

        for endPointDpid in sla.endPointsDpid:
            self.getSrcToDestPath(endPointDpid, CLOUD_DPID)

        # Retrieve Cloud Hypervisor IP and sockfd
        hypIPAddr = self.m_dpid_to_hyp_ip[CLOUD_DPID]
        cloudSockfd = ""
        for pair in self.m_hyp_ip_sockfd_pair:
            if hypIPAddr == pair.val1[0]:
                cloudSockfd = pair.val2
                break

        # Sanity Check
        if cloudSockfd == "":
            LOG_DEBUG("Incorrect Migration to Cloud Hypervisor(%s) or System communication with Hypervisor(%s) is broken." % (CLOUD_DPID, CLOUD_DPID))
            return FAILURE

        # Move all VNFs of the SLA
        for index in range(0, len(sla.VNFIds)):
            old_dpid   = sla.VNFsNetworkDpid[index]
            oldVNFInfo = gUsedVNFIds[sla.VNFIds[index]]

            # Rest of the Actions to be taken after VNF comes up at the New Hypervisor
            # Ref: migrateToCloud_SLARestOp

            ## Step 1 : Save current context
            if sla.identifier not in self.m_SLACloudOperationsOnStart:
                self.m_SLACloudOperationsOnStart[sla.identifier]                = {}
                self.m_SLACloudOperationsOnStart[sla.identifier]['VNFsMac']     = copy.deepcopy(sla.VNFsNetworkMac)
                self.m_SLACloudOperationsOnStart[sla.identifier]['VNFsDpid']    = copy.deepcopy(sla.VNFsNetworkDpid)
                self.m_SLACloudOperationsOnStart[sla.identifier]['VNFRemCount'] = len(sla.vnfInputList)
                self.m_SLACloudOperationsOnStart[sla.identifier]['VNFsId']      = copy.deepcopy(sla.VNFIds)

            newVNFInfo = self.assignVNFResources(sla, index, CLOUD_DPID, True)

            self.m_vnfOperationsOnStart[newVNFInfo.macAddr] = {}
            self.m_vnfOperationsOnStart[newVNFInfo.macAddr]['old_dpid']  = old_dpid
            self.m_vnfOperationsOnStart[newVNFInfo.macAddr]['old_mac']   = oldVNFInfo.macAddr
            self.m_vnfOperationsOnStart[newVNFInfo.macAddr]['old_vnfId'] = oldVNFInfo.identifier
            self.m_vnfOperationsOnStart[newVNFInfo.macAddr]['new_vnfId'] = newVNFInfo.identifier            

            ## Step 2a : Start VNF at the Nbr Hypervisor with same configuration
            # Starts VNF at the Hypervisor
            self.sendStartVNFCommand(newVNFInfo, cloudSockfd)

            ## Step 2b : Forwarding Msg Command
            self.sendForwardingVNFCommand(sla, newVNFInfo, cloudSockfd, index)

   
    # Handles remaining steps of migration of entire SLA (associated VNFs) to the Cloud
    # Scope : Completes all other operations for Migration
    def migrateToCloud_SLARestOp(self, newVNFInfo, savedContext):

        sla = self.m_SLAs[newVNFInfo.slaIdentifier]

        savedContext['VNFRemCount'] -= 1

        # Install Flow Rules after all VNFs in the Cloud have started
        if savedContext['VNFRemCount'] != 0:
            return

        oldVNFNetworkMacs = copy.deepcopy(savedContext['VNFsMac'])
        oldVNFNetworkDpid = copy.deepcopy(savedContext['VNFsDpid'])
        oldVNFIds         = copy.deepcopy(savedContext['VNFsId'])

        ## Step 2 : Update Complete Path of SLA
        self.updateCompPathOfSLAInCloud(sla)

        ## Step 3: Update VNF Information w.r.t. New Dpid in all related data-structures
        for index in range(0, len(sla.VNFsNetworkDpid)):
            sla.VNFsNetworkDpid[index] = new_dpid
            newVNFInfo.dpid            = new_dpid
        
        # Map VNFInfo to New Hypervisor
        self.m_hypVNFStatus[newVNFInfo.dpid].append(newVNFInfo.identifier)
        self.m_hypervisorMemStats[new_dpid]['used'] += newVNFInfo.cpuMemReq
        self.m_hypervisorMemStats[old_dpid]['used'] -= newVNFInfo.cpuMemReq

        ## Step 4 : Add New flow rules for this change with Higher Priority
        self.updateNewSLAFlowRules(sla, True, [], [])
        LOG_DEBUG("Installed New SLA Flow Rules for the SLA (%s) moved to the Cloud." % sla.identifier)

        ## Step 5: Stop VNF at the old Hypervisor
        for index in range(0, len(oldVNFNetworkDpid)):
            oldDpid    = oldVNFNetworkDpid[index]
            oldVNFInfo = gUsedVNFIds[oldVNFIds[index]]
            
            hypIPAddr = self.m_dpid_to_hyp_ip[oldDpid]
            oldSockfd = ""
            for pair in self.m_hyp_ip_sockfd_pair:
                if hypIPAddr == pair.val1[0]:
                    oldSockfd = pair.val2
                    break

            # Sanity Check
            if oldSockfd == "":
                LOG_DEBUG("System communication with Old Hypervisor(%s) is broken. Migration Failed." % (new_dpid.dpid))
                return FAILURE

            # Stops VNF at the Old Hypervisor
            self.sendStopVNFCommand(oldVNFInfo, oldSockfd)

            ## Step 6: Remove Previous Flow Rules for all paths
            if sla.compPathOfSLA[src_mac][dst_mac]['prevPath'] != []:

                self.removeOldSLAFlowRules(sla, src_mac, dst_mac, sla.compPathOfSLA[src_mac][dst_mac]['prevPath'], oldVNFsNetworkDpid, oldVNFsNetworkMac)
                sla.compPathOfSLA[src_mac][dst_mac]['prevPath'] = []

        
            ## Step 7: Update VNF Information w.r.t. Old Dpid in all related data-structures
            del self.m_mac_to_dpid_port[oldVNFInfo.macAddr]
            del self.m_dpid_to_mac_port[old_dpid][oldVNFInfo.macAddr]
            self.m_hypVNFStatus[old_dpid].remove(oldVNFInfo.identifier)

        # Remove entry
        del self.m_SLACloudOperationsOnStart[newVNFInfo.slaIdentifier]

        # Yipee... SLA is properly migrated to the Cloud
        LOG_INFO("Successful Migration of SLA (%s) from Hypervisor(%s) to Cloud Hypervisor(%s)" % 
                 (sla.identifier, oldVNFInfo.identifier, old_dpid, newVNFInfo.identifier, CLOUD_DPID))

    # Moves a VNF and its entire SLA Chain to the Cloud
    def handleNodeBottleneckCase3(self, dpid):

        # All VNFs installed at the Bottlenecked Hypervisor
        # TODO: Picks the First VNF and its associated SLA as Victim
        for vnfIndex in self.m_hypVNFStatus[dpid]:
            vnfInfo = gUsedVNFIds[vnfIndex]
            sla = self.m_SLAs[vnfInfo.slaIdentifier]
            LOG_INFO("Hypervisor (%s) : SLA (%s) considered for Migration to Cloud (Case 3)." % (dpid, vnfInfo.identifier))

        # Migrate the selected SLA to the Cloud
        self.migrateToCloud_SLAStartOp(sla)

    # -----------------------------------------
    # Miscellaneous Functions
    # -----------------------------------------

    # Reads Hypervisor Configuration File
    def read_HYP_config_file(self):
        dpid_ip_pair = {}

        file = open(HYPERVISOR_CONFIGURATION_FILE, "r")

        # Retreive # No.of nodes
        nodes = int(file.readline().rstrip())
        for i in range(nodes):
            line = file.readline().strip()

            # Retreive dpid and Hypervisor IP
            words = line.split()
            dpid_ip_pair[int(words[0])] = words[1].strip("\n")

        return dpid_ip_pair

def LOG_INFO(string):
    print str(string) + " - " + str(currentframe().f_back.f_lineno)

def LOG_DEBUG(string):
    print str(string) + " - " + str(currentframe().f_back.f_lineno)

def LOG_DEVEL(string):
    return
    print str(string) + " - " + str(currentframe().f_back.f_lineno)

def LOG_ERROR(string):
    print str(string) + " - " + str(currentframe().f_back.f_lineno)

class make_tuple():

    def __init__(self, value1, value2, value3=None):
        self.val1 = value1
        self.val2 = value2
        self.val3 = value3

def print_flowpath(path):

    print "----------------------------"
    print path
    x = ""

    for item in path:
        x += " -> %s" % item
    LOG_DEBUG("Flowpath: %s" % x)
    print "----------------------------"

def reverse_flowpath(path):
    retList = []
    for item in range(len(path)-1, -1, -1):
        retList.append(path[item])

    return retList

