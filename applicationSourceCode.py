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
alpha = 0.6
beta  = 0.2
gamma = 0.2

# Output Filenames
THROUGHPUT_ANIM_FILENAME = "throughput.json"
LATENCY_ANIM_FILENAME    = "latency.json"
CPU_ANIM_FILENAME        = "cpu.json"

LOG_PLACEMENT_FILENAME   = "log-placement-sla.txt"
LOG_BOTTLENECK_FILENAME  = "log-bottleneck.txt"
LOG_BANDWIDTH_FILENAME   = "log-bandwidth.txt"

LINK_LATENCY_ETH_TYPE   = 0x07c3
SWITCH_LATENCY_ETH_TYPE = 0x07c4

# TODO Hypervisor CPU Memory # In MB
DOCKER_CONT_MEM_LIMIT          = 512
HOST_CONT_MEM_LIMIT            = 200

LINK_BW_LIMIT = 500 # 300 Mbps
LINK_BW_THRESHOLD = 0.98

# Timeout till the SLA agrrement starts coming
SLA_INPUT_TIMEOUT      = 12
MONITORING_LOG_TIMEOUT = 5

# Total VNFs installed
gUsedVNFIds   = {}
gUsedVNFCount = 0

# Bottleneck Ids
gBottlenecks = {}
gBottleneckCount = 0

# Docker SubNet
DOCKER_SUB_NET      = "192.168.111."
DOCKER_SUBNET_NAME  = 'overnet'

# Configuration File
SLA_CONFIGURATION_FILE        = "sla_input.txt"
HYPERVISOR_CONFIGURATION_FILE = "hyp_config.txt"

# Miscellaneous 
SUCCESS = 1
FAILURE = 0

LOGGING_DEBUG = False
LOGGING_INFO  = 0

COLOR_WHITE = 0
COLOR_BLACK = 1

IPERF_DURATION = 1000

#### GLOBAL VARIABLES

# Prioirty Level
START_PRIORITY_VAL = 65500

# Cloud DPID
CLOUD_DPID = 9

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
        self.placementTimeData  = {}             # Run-time data for Placement

        
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

        # Logging Module
        self.DLOG_Thread()

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
        self.m_linkNbrs               = {}

        self.m_spTreeLinks = {}
        self.m_cloudLinks  = {}

        self.m_mac_to_dpid_port = {}
        self.m_dpid_to_mac_port = {}

        self.m_vnfOperationsOnStart       = {}
        self.m_SLACloudOperationsOnStart  = {}
        self.m_SLAMultiMigrationOpOnStart = {}

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

    def mapLinkNbrs(self):
        self.m_linkNbrs = {}

        # Create link information for all Dpids
        for dpid in self.m_graph['edges']:

            if dpid not in self.m_linkNbrs:
                self.m_linkNbrs[dpid] = {}

                # Retrieve Nbrs of the current Dpid
                for nbr_dpid,out_port in self.m_graph['edges'][dpid].items():

                    if out_port not in self.m_linkNbrs[dpid]:
                        self.m_linkNbrs[dpid][out_port] = -1

                    self.m_linkNbrs[dpid][out_port] = nbr_dpid

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
                self.m_linkLatencyStats[src_dpid][dst_dpid]['max']       = float(0.0)

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
    #    LOGGING MODULE : Logs Current Monitoring Information
    # -------------------------------------------------------------------------------------------------------------------------

    # Creates the Thread for logging periodic Monitored information
    def DLOG_Thread(self):
        self.DLOG_logThread = hub.spawn(self._monitoredInfoLogThread)

    def _monitoredInfoLogThread(self):
        hub.sleep(MONITORING_LOG_TIMEOUT)

        # Initiliaze the File
        self.write_to_file(LOG_BANDWIDTH_FILENAME, "", 'w')

        hub.sleep(30)

        # Tweak : MCase Node Bottleneck
        if len(self.m_SLAs) == 0:
            LOG_INFO("No SLAs installed to tweak Bottleneck Scenario.")
        elif 1:
            if 1:
                bottleneckedDpid = 7
                LOG_INFO("Tweaked: Bottleneck detected at Hypervisor(%s)." % bottleneckedDpid)
                self.handleNodeBottleneck(bottleneckedDpid)
            else:
                for index in range(1, len(self.m_SLAs) + 1):
                    sla = self.m_SLAs[index]
                    if True and sla.VNFsNetworkDpid[0] != CLOUD_DPID:
                        bottleneckedDpid = sla.VNFsNetworkDpid[0]
                        LOG_INFO("Tweaked: Bottleneck detected at Hypervisor(%s)." % bottleneckedDpid)
                        self.handleNodeBottleneck(bottleneckedDpid)
                        break

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
        self.readSLAList()

        # Wait for all Hosts of the SLAs to be active
        usersToBeActive = {}
        for key,sla in self.m_SLAs.items():
            for index in range(0, len(sla.endPointsDpid)):
                mac  = sla.endUsersMac[index]
                dpid = sla.endPointsDpid[index]

                usersToBeActive[mac] = dpid

        # Wait for all Users of the SLA are active
        while len(usersToBeActive):
            hub.sleep(1.5)
            for mac, dpid in usersToBeActive.items():

                if dpid in self.m_graph['hosts'] and mac in self.m_graph['hosts'][dpid]:
                    del usersToBeActive[mac]

        LOG_DEBUG("All Hosts of SLAs are up.")

        for key,sla in self.m_SLAs.items():

            sla.placementTimeData['startTime'] = time.time()

            # Creates reverse Map of EndPoints to SLAs
            self.mapEndUsersToSLAs(sla)

            # Algorithm - 1 : Placement of the SLA
            self.placementOfSLA_StartOp(sla)

            hub.sleep(2)

    # Reads SLAs to be installed over the network
    def readSLAList(self):
        
        skipFirstLine = True
        chars_to_remove      = ['[', ']', '\'']
        temp_chars_to_remove = ['[', ']']

        with open(SLA_CONFIGURATION_FILE,'rb') as file:
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

                # CPU Mem requirement of VNFs
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

                    # Update Mem used by the End-Hosts of the SLA at their respective dpid's
                    self.m_hypervisorMemStats[dpids[index]]['used'] += HOST_CONT_MEM_LIMIT

                if len(macAddrs) != len(dpids):
                    print "Error: Incorrect SLA, Count of MAC Addr and their Dpids do not match. Ignoring the SLA..."
                    continue

                self.m_SLAsCount = self.m_SLAsCount + 1

                sla = struct_SLA(self.m_SLAsCount, vnfTypes, vnfsMemReq, delayTolerated, reqBW, macAddrs, dpids)
                self.m_SLAs[self.m_SLAsCount] = sla

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

        if False and LOGGING_DEBUG:
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
                return

            bandwidthAcheived = float(deltaBytesProcessed * 8)/float(float(UNIT_OF_BANDWIDTH) * float(deltaTime)) # Kbps
            self.m_switchFlowStats[dpid][port]['data'] = [durationFromStart, bandwidthAcheived]

            self.m_switchFlowStats[dpid][port]['LastTotalBytes']   = currentBytesProcessed
            self.m_switchFlowStats[dpid][port]['LastRecordedTime'] = currentTime

            self.write_to_file(THROUGHPUT_ANIM_FILENAME, self.m_switchFlowStats)

            if dpid in self.m_linkNbrs and port in self.m_linkNbrs[dpid]:
                nbr_dpid = self.m_linkNbrs[dpid][port]
                # For only one way log is done
                if dpid > nbr_dpid:
                    logBandwidthData = "%s %s %s %s" % (dpid, nbr_dpid, durationFromStart, bandwidthAcheived)
                    self.write_to_file(LOG_BANDWIDTH_FILENAME, logBandwidthData, 'a')

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
            self.m_linkLatencyStats[dpid1][dpid2]['max']            = max(self.m_linkLatencyStats[dpid1][dpid2]['data'], 
                                                                          self.m_linkLatencyStats[dpid1][dpid2]['max'])
            self.write_to_file(LATENCY_ANIM_FILENAME, self.m_linkLatencyStats)

    # Function writes data to a file
    def write_to_file(self, fileName, data, openMode='w'):
        fileType = fileName.split('.')[1]

        if fileType == 'json':
            with open(fileName, mode=openMode) as outfile:
                json.dump(data, outfile)

        elif fileType == 'txt':
            with open(fileName, mode=openMode) as outfile:
                outfile.write(data + '\n')

        else:
            LOG_ERROR("Invalid write to file. File type not supported")

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
                    if in_port != out_port and nbr_dpid in self.m_cloudLinks and dpid in self.m_cloudLinks[nbr_dpid]:
                        actions.append(datapath.ofproto_parser.OFPActionOutput(out_port))
                        sendPktOutFlag = True

            # Forwarding to the hosts
            if dpid in self.m_graph['hosts']:
                for mac,out_port in self.m_graph['hosts'][dpid].items():
                    if out_port != in_port:
                        actions.append(datapath.ofproto_parser.OFPActionOutput(out_port))
                        sendPktOutFlag = True

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

    # Assign VNF Resources
    def assignVNFResources(self, sla, index, dpid, isMigrated):
        global gUsedVNFIds, gUsedVNFCount

        gUsedVNFCount += 1

        # Find the VNF Id not in use
        for item, val in gUsedVNFIds.items():
            if gUsedVNFIds[item] == False and item >= 60: # TODO
                vnfId = item
                break

        ipAddr  = DOCKER_SUB_NET + str(vnfId)
        macAddr = "00:00:00:00:00:" + str(vnfId).zfill(2)

        # Update VNF MAC for the Migrated VNF
        if isMigrated:
            sla.VNFsNetworkMac[index]  = macAddr
            sla.VNFsNetworkDpid[index] = dpid
            sla.VNFIds[index]          = vnfId
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
        if vnfId in sla.VNFIds:
            sla.VNFIds.remove(vnfId)

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

        # Firewall
        if container_type == "firewall":
            cont_ip   = "192.168.111.%s" % (container_id)
            msgs.append("docker run -d --mac-address=\"%s\" --name %s -m %sm --network=%s --ip=%s --privileged kalilinux/kali-linux-docker:latest sleep 10000" % (cont_mac, cont_name, DOCKER_CONT_MEM_LIMIT, DOCKER_SUBNET_NAME, cont_ip))
            msgs.append("docker exec %s echo 0 > /proc/sys/net/ipv4/conf/all/accept_redirects" % cont_name)
            msgs.append("docker exec %s echo 0 > /proc/sys/net/ipv4/conf/all/send_redirects" % cont_name)            

        # BusyBox
        elif container_type == "busy_box":
            cont_ip   = "192.168.111.%s" % (container_id)
            msgs.append("docker run -d --mac-address=\"%s\" --name %s -m %sm --network=%s --ip=%s centos:latest sleep 10000" % (cont_mac, cont_name, DOCKER_CONT_MEM_LIMIT, DOCKER_SUBNET_NAME, cont_ip))

        else:
            LOG_DEBUG("Container %s not supported." % container_type)

        # Send Message to Hypervisor
        for msg in msgs:
            sockfd.send(msg)

    # Creates message to Stop VNF at Hypervisor
    def sendStopVNFCommand(self, vnfInfo, sockfd):
        cont_name = "c%s" % (vnfInfo.identifier)

        # Force the removal of a running container (uses SIGKILL)
        msg = "docker rm --force %s" % cont_name

        # Send Message to Hypervisor
        sockfd.send(msg)

    # Creates message for Forwarding in VNFs
    def sendForwardingVNFCommand(self, sla, vnfInfo, sockfd, serviceChainIndex):
        container_type = vnfInfo.vnfType.lower()
        container_id   = vnfInfo.identifier
        cont_name      = "c%s" % (container_id)
        cont_mac       = vnfInfo.macAddr
        cont_ip        = vnfInfo.ipAddr

        msgs = []

        msgs.append("docker exec %s echo 1 > /proc/sys/net/ipv4/ip_forward" % cont_name)
        msgs.append("docker exec %s iptables -F" % cont_name)
        msgs.append("docker exec %s iptables -A OUTPUT -j DROP" % cont_name)
        msgs.append("docker exec %s iptables -A FORWARD -i eth0 -o eth0 -j ACCEPT" % cont_name)

        # Send Messages to Hypervisor
        for msg in msgs:
            sockfd.send(msg)

    # Installs VNFs at their respective Hypervisors
    # Used only during Placement Algorithm
    def installVNFsAtHypervisors(self, sla, toBeInstalledVNFInfo):

        ## Step - 2: Start Msg Command
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

        ## Step - 3 : Forwarding Msg Command
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

    # Logs Placement Information about the SLA
    def logPlacementInfo(self, sla, startTime, vnfInstallStart, flowRulesInstallStart, endTime):
        infos = []

        infos.append("\n")
        infos.append("CHAIN LENGTH : %s" % len(sla.vnfInputList))
        infos.append("SLA ID: %s" % sla.identifier)
        infos.append("PLACED: %s" % ("CLOUD" if sla.VNFsNetworkDpid[0] == CLOUD_DPID else "FOG-EDGE"))
        infos.append("ALGO-RUNTIME: %s" % str(float(vnfInstallStart) - float(startTime)))
        infos.append("VNF-INSTALL-TIME: %s" % str(float(flowRulesInstallStart) - float(vnfInstallStart)))
        infos.append("FLOWS-INSTALL-TIME: %s" % str(float(endTime) - float(flowRulesInstallStart)))
        infos.append("TOTAL-TIME: %s" % str(float(endTime) - float(startTime)))

        for info in infos:
            self.write_to_file(LOG_PLACEMENT_FILENAME, info, 'a')

    # Stop temp running Host and starts Iperf Host for communication
    # Reason - On starting IPerf Host, it tries to communicate with the Server immediately,
    # Flow rules are not installed by that time
    def startHostTraffic(self, sla):

        # Assuming the First Host as the Iperf client
        src_hostIndex = 0
        dst_hostIndex = 1

        src_hostDpid = sla.endPointsDpid[src_hostIndex]

        # Retrieve Hypervisor IP
        hypIPAddr = self.m_dpid_to_hyp_ip[src_hostDpid]
        sockfd    = ""

        for pair in self.m_hyp_ip_sockfd_pair:
            if hypIPAddr == pair.val1[0]:
                sockfd = pair.val2
                break

        # Sanity Check
        if sockfd == "":
            LOG_DEBUG("%s" % str(self.m_hyp_ip_sockfd_pair))
            LOG_ERROR("Incorrect placement at Hypervisor (%s) or System communication with Hypervisor(%s) is broken." % (src_hostDpid, src_hostDpid))
            return FAILURE
 
        srcHostMacAddr = sla.endUsersMac[src_hostIndex]
        srcHostId      = int(srcHostMacAddr.split(":")[5])
        srcHostName    = "c%s" % (srcHostId)
        srcHostIP      = "192.168.111." + "%s" % (srcHostId)

        dstHostMacAddr = sla.endUsersMac[dst_hostIndex]
        dstHostId      = int(dstHostMacAddr.split(":")[5])
        dstHostIP      = "192.168.111." + "%s" % (dstHostId)

        msgs = []

        # Step - 1: Stop and Remove existing Host container
        msgs.append("docker stop %s" % (srcHostName))
        msgs.append("docker rm %s" % (srcHostName))

        # Step - 2: Start Host as Iperf Client Traffic
        msgs.append("docker run -t -d --name=%s --network=%s --mac-address=\"%s\" --ip=\"%s\" --privileged networkstatic/iperf3:latest -c %s -t %s" % (srcHostName, DOCKER_SUBNET_NAME, srcHostMacAddr, srcHostIP, dstHostIP, IPERF_DURATION))
        #msgs.append("docker exec %s tail -f /dev/null" % (srcHostName)) # To run iperf client in foreground

        # Send Message to Hypervisor
        for msg in msgs:
            sockfd.send(msg)

        LOG_INFO("Hosts of SLA (%s) to start Iperf Traffic." % (sla.identifier))

    # Rest operations of the Placement Algorithm
    def placementOfSLA_RestOp(self, newVNFInfo):

        sla = self.m_SLAs[newVNFInfo.slaIdentifier]

        # Check whether all VNFs are active
        vnfsActive = 0
        for index in range(0, len(sla.VNFsNetworkMac)):
            mac  = sla.VNFsNetworkMac[index]
            dpid = sla.VNFsNetworkDpid[index]

            if dpid in self.m_graph['hosts'] and mac in self.m_graph['hosts'][dpid]:
                vnfsActive += 1

        if vnfsActive != len(sla.VNFsNetworkDpid):
            return     
        
        # Analysis of Placement Algorithm
        flowRulesStartTime = time.time()
        
        # Step 4: Installation of the respective flow Rules will be done here
        self.updateNewSLAFlowRules(sla)

        LOG_INFO("SLA (%s) is installed over the Network with the VNFs placed at"
                  " Hypervisors (%s) having VNF Ids (%s)." % 
                  (sla.identifier, sla.pathOfServiceChain, sla.VNFIds))

        # Log Placement Time of SLA
        placementEndTime = time.time()

        # Log Placement Information for the SLA
        self.logPlacementInfo(sla, sla.placementTimeData['startTime'], sla.placementTimeData['vnfInstallStart'], flowRulesStartTime, placementEndTime)

        # Yes Yes Yes... SLA is properly mapped over the Network
        sla.isInstalled = True

        # Stop and Start one of the Host as IPerf Client
        self.startHostTraffic(sla)

        '''
        count = 0
        for index in range(1, len(self.m_SLAs)+1):
            sla = self.m_SLAs[index]
            if sla.isInstalled:
                count += 1
        if count == len(self.m_SLAs):
            bottleneckedDpid = 7
            LOG_INFO("Tweaked: Bottleneck detected at Hypervisor(%s)." % bottleneckedDpid)
            self.handleNodeBottleneck(bottleneckedDpid)
        '''

    def generatePathOfSLA(self, sla, isPlacedAtCloud):
        
        allPaths = {}

        for src_mac in sla.endUsersMac:
            for dst_mac in sla.endUsersMac:

                # Sanity Check
                if src_mac == dst_mac:
                    continue

                path = []

                src_dpid = self.m_mac_to_dpid_port[src_mac].val1
                dst_dpid = self.m_mac_to_dpid_port[dst_mac].val1

                # Forward Path of Service Chain

                # Add Src Dpid
                path.append([src_dpid, -1])

                # Src To 1st VNF
                src_to_vnf_path = self.getSrcToDestPath(src_dpid, CLOUD_DPID if isPlacedAtCloud else sla.VNFsNetworkDpid[0])

                if len(src_to_vnf_path) > 2:
                    for inner_index in range(1, len(src_to_vnf_path) - 1):
                        inner_dpid = src_to_vnf_path[inner_index]
                        path.append([inner_dpid, 0])

                # Intermediate VNFs
                if isPlacedAtCloud:
                    path.append([CLOUD_DPID, len(sla.vnfInputList)])

                else:
                    for index in range(0, len(sla.VNFsNetworkDpid)-1):
                        flow_path = self.getSrcToDestPath(sla.VNFsNetworkDpid[index], sla.VNFsNetworkDpid[index+1])
                        path.append([flow_path[0], 1]) # Src Dpid
                        # Skip Dst Dpid, gets added in next iteration
                        for inner_index in range(1, len(flow_path)-1):
                            inner_dpid = flow_path[inner_index]
                            path.append([inner_dpid, 0])

                    # Add the Last VNF Dpid
                    path.append([sla.VNFsNetworkDpid[-1], 1])

                # Last VNF to Dst
                dst_to_vnf_path = self.getSrcToDestPath(CLOUD_DPID if isPlacedAtCloud else sla.VNFsNetworkDpid[-1], dst_dpid)
                for inner_index in range(1, len(dst_to_vnf_path)-1):
                        inner_dpid = dst_to_vnf_path[inner_index]
                        path.append([inner_dpid, 0])

                # Add Dst Dpid
                path.append([dst_dpid, -1])

                # Club duplicate entries, if exists
                path = self.mergeDuplicateEntries(path)

                # Complete Path of SLA from Srouce to Destination
                if src_mac not in allPaths:
                    allPaths[src_mac] = {}

                if dst_mac not in allPaths[src_mac]:
                    allPaths[src_mac][dst_mac] = {}

                allPaths[src_mac][dst_mac]['prevPath'] = []
                allPaths[src_mac][dst_mac]['currPath'] = path
                allPaths[src_mac][dst_mac]['priority'] = START_PRIORITY_VAL
 
                # Path of Reverse SLA Chain
                if self.debugFlag:
                    LOG_DEVEL("For Hosts %s -> %s: " % (src_mac, dst_mac))
                    LOG_DEVEL("Previous Forward Path: %s" % allPaths[src_mac][dst_mac]['prevPath'])
                    LOG_DEVEL("Current Forward Path: %s" % allPaths[src_mac][dst_mac]['currPath'])
                
                ### Reverse Path of Service Chain
                VNFsNetworkDpid = copy.deepcopy(sla.VNFsNetworkDpid)
                VNFsNetworkDpid.reverse()

                path = []
 
                temp_dpid = src_dpid
                src_dpid = dst_dpid
                dst_dpid = temp_dpid

                # Add Src Dpid
                path.append([src_dpid, -1])

                # Src To 1st VNF
                src_to_vnf_path = self.getSrcToDestPath(src_dpid, CLOUD_DPID if isPlacedAtCloud else VNFsNetworkDpid[0])

                if len(src_to_vnf_path) > 2:
                    for inner_index in range(1, len(src_to_vnf_path) - 1):
                        inner_dpid = src_to_vnf_path[inner_index]
                        path.append([inner_dpid, 0])
                
                if isPlacedAtCloud:
                    path.append([CLOUD_DPID, len(sla.vnfInputList)])

                else:
                    # Intermediate VNFs
                    for index in range(0, len(VNFsNetworkDpid)-1):
                        flow_path = self.getSrcToDestPath(VNFsNetworkDpid[index], VNFsNetworkDpid[index+1])
                        path.append([flow_path[0], 1]) # Src Dpid
                        # Skip Dst Dpid, gets added in next iteration
                        for inner_index in range(1, len(flow_path)-1):
                            inner_dpid = flow_path[inner_index]
                            path.append([inner_dpid, 0])

                    # Add the Last VNF Dpid
                    path.append([VNFsNetworkDpid[-1], 1])

                # Last VNF to Dst
                dst_to_vnf_path = self.getSrcToDestPath(CLOUD_DPID if isPlacedAtCloud else VNFsNetworkDpid[-1], dst_dpid)
                for inner_index in range(1, len(dst_to_vnf_path)-1):
                        inner_dpid = dst_to_vnf_path[inner_index]
                        path.append([inner_dpid, 0])

                # Add Dst Dpid
                path.append([dst_dpid, -1])

                # Club duplicate entries, if exists
                path = self.mergeDuplicateEntries(path)

                allPaths[src_mac][dst_mac]['prevRevPath'] = []
                allPaths[src_mac][dst_mac]['currRevPath'] = path

                # Path of Reverse SLA Chain
                if self.debugFlag:
                    LOG_DEVEL("For Hosts %s -> %s: "  % (src_mac, dst_mac))
                    LOG_DEVEL("Previous Rev Path: %s" % allPaths[src_mac][dst_mac]['prevRevPath'])
                    LOG_DEVEL("Current Rev Path: %s"  % allPaths[src_mac][dst_mac]['currRevPath'])

        return allPaths

    # Placement of SLA
    # Scope limited to starting of the VNFs at the Hypervisor
    # Ref : placementOfSLA_RestOp
    def placementOfSLA_StartOp(self, sla):

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

                #for vVertex in self.m_graph['edges'][uVertex]:
                for vVertex in self.m_spTreeLinks[uVertex]:

                    # Do not consider the Parent vertex
                    if vVertex == dctEndPoints[endPoint]['parent'][uVertex] or uVertex == dctEndPoints[endPoint]['parent'][vVertex] or vVertex == CLOUD_DPID:
                        continue

                    # Check for constraints
                    if vVertex not in dctEndPoints[endPoint]['visited'] and endPoint not in seenEndPoints[vVertex]:

                        # Push into the Queue
                        dctEndPoints[endPoint]['queue'].append(vVertex)

                        # Update Parent Pointer
                        dctEndPoints[endPoint]['parent'][vVertex] = uVertex

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

                        # 'C2' (Dynamic Constraint) : Constraint for Link's Available BW
                        try:
                            uVertex_to_vVertexPort = self.m_graph['edges'][uVertex][vVertex]

                            linkBandwidthAchieved  = self.m_switchFlowStats[uVertex][uVertex_to_vVertexPort]['data'][1]

                            if sla.reqBW > LINK_BW_THRESHOLD * (LINK_BW_LIMIT - linkBandwidthAchieved):
                                continue
                        except:
                            pass
                        

                        # 'C3' (Static Constraint)  : Constraint for CPU utilization 
                        if cpuMemReq > (self.m_hypervisorMemStats[vVertex]['capacity'] - self.m_hypervisorMemStats[vVertex]['used']):
                            continue

                        # Add EndPoint to Seen DS
                        seenEndPoints[vVertex].append(endPoint)

                        # Check whether all End points are observed
                        # Do Not choose Cloud as centre during Placement
                        # Do not map any VNF at the Hypervisor of the Hosts, Technical limitation
                        # pxxx  
                        if len(seenEndPoints[vVertex]) == len(sla.endPointsDpid) and vVertex != CLOUD_DPID and vVertex not in sla.endPointsDpid:

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
            LOG_DEBUG("SLA (%s) cannot be placed in the Current Network. Moving the entire SLA to the Cloud." % sla.identifier)
            self.placementToCloud_SLAStartOp(sla)
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
                # 'C1' (Static Constraint)  : Constraint for CPU Memory Status

                if cpuMemReq <= (self.m_hypervisorMemStats[dpid]['capacity'] - self.m_hypervisorMemStats[dpid]['used']):

                    toBeInstalledVNFInfo.append(self.assignVNFResources(sla, index, dpid, False))
                    
                # Case 2 : Map to neighbors within Link Latency constraints
                else:
                   
                    # Retreive Link latency
                    nbr_latency = {}
                    for nbr_dpid in self.m_graph['edges'][dpid]:

                        # Do not map any VNF at the cloud
                        # Do not map any VNF at the Hypervisor of the Hosts, Technical limitation
                        # xxx
                        if nbr_dpid == CLOUD_DPID or nbr_dpid in sla.endPointsDpid:
                            continue

                        linkLatency = 0.0
                        # 'C1' (Dynamic Constraint) - Constraint for Edge's Latency/Delay
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
                        try:
                            dpid_to_nbrDpid_port = self.m_graph['edges'][dpid][nbr_dpid]
                            linkBandwidthAchieved  = self.m_switchFlowStats[uVertex][dpid_to_nbrDpid_port]['data'][1]

                            if sla.reqBW > LINK_BW_THRESHOLD * (LINK_BW_LIMIT - linkBandwidthAchieved):
                                continue

                        except:
                            pass
                        
                        # All Constraints satisfied...
                        nbr_latency[nbr_dpid] = linkLatency

                    # Sanity Check
                    if len(nbr_latency) == 0:
                        LOG_DEBUG("VNF(%s) of SLA (%s) cannot be placed at any Nbrs of %s." % (index, sla.identifier, dpid))
                        LOG_DEBUG("SLA (%s) cannot be placed in the Current Network. Moving the entire SLA to the Cloud." % (sla.identifier))

                        # Recover assigned Resources
                        for vnfInfo in toBeInstalledVNFInfo:
                            self.recoverVNFResources(sla, vnfInfo)

                        self.placementToCloud_SLAStartOp(sla)
                        return

                    # Greedy Approach : Choose the Neighbor with minimum Latency
                    minLatency = float("inf")
                    #xxx
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
            
            LOG_INFO("SLA (%s) to be placed at Hypervisor(s) (%s) with overall Delay Buffer (%s)." % (sla.identifier, sla.pathOfServiceChain, sla.delayBuffer))
        
        # Note the complete path of the SLA in the network for all Hosts in the SLA
        sla.compPathOfSLA = self.generatePathOfSLA(sla, False)

        # Rest Operations to be performed when all the VNFs have started
        # Ref : placementOfSLA_RestOp
        # Step 3: Save current context
        for newVNFInfo in toBeInstalledVNFInfo:

            # Sanity Check
            if newVNFInfo.macAddr in self.m_vnfOperationsOnStart:
                LOG_ERROR("This scenario should not occur. Programming Error!!!")
                return

            self.m_vnfOperationsOnStart[newVNFInfo.macAddr]                = {}
            self.m_vnfOperationsOnStart[newVNFInfo.macAddr]['new_vnfId']   = newVNFInfo.identifier
            self.m_vnfOperationsOnStart[newVNFInfo.macAddr]['scenario']    = "placement"

        sla.placementTimeData['vnfInstallStart'] = time.time()

        # Step 4: Install VNFs at their assigned Hypervisor's
        if FAILURE == self.installVNFsAtHypervisors(sla, toBeInstalledVNFInfo):
            LOG_ERROR("SLA (%s) cannot be placed in the Current Network. System issue!!!" % (sla.identifier))

            # Recover assigned Resources
            for vnfInfo in toBeInstalledVNFInfo:
                self.recoverVNFResources(sla, vnfInfo)
                
            return

    # Checks whether SLA Delay Tolerated is within constraints of Placement to the Cloud
    def checkSLADelayWithInCloud(self, sla):

        # Retreive all paths from Host Dpid to the Cloud
        hostDpidToCloudPath = {}
        for endPointDpid in sla.endPointsDpid:
            hostDpidToCloudPath[endPointDpid] = self.getSrcToDestPath(endPointDpid, CLOUD_DPID)

        # Calculate Delay from Host Dpid to the Cloud
        delayHostToCloud = {}
        for endPointdpid,path in hostDpidToCloudPath.items():

            totalLinkLatency = float(0.0)
            for index in range(0, len(path)-1):
                dpid     = path[index]
                nbr_dpid = path[index + 1]

                if dpid in self.m_linkLatencyStats and nbr_dpid in self.m_linkLatencyStats[dpid]:
                    totalLinkLatency += self.m_linkLatencyStats[dpid][nbr_dpid]['data']

                elif nbr_dpid in self.m_linkLatencyStats and dpid in self.m_linkLatencyStats[nbr_dpid]:
                    totalLinkLatency += self.m_linkLatencyStats[nbr_dpid][dpid]['data']

            delayHostToCloud[endPointdpid] = totalLinkLatency

        # Communication is between two Hosts, 
        # hence delay between all pairs of Hosts to be considered
        for dpid,dpid_delay in delayHostToCloud.items():
            for nbr_dpid, nbr_dpid_delay in delayHostToCloud.items():

                if dpid == nbr_dpid:
                    continue

                if dpid_delay + nbr_dpid_delay > sla.delayTolerated:
                    LOG_DEBUG("SLA cannot be placed at the Cloud, delay constraint violated.")
                    pdb.set_trace()
                    return FAILURE

        return SUCCESS

    # Handles placement of entire SLA (associated VNFs) to the Cloud
    # Scope limited to Updating Complete Paths and starting VNF(s) at the Cloud
    def placementToCloud_SLAStartOp(self, sla):

        # TODO: Check SLA is within Delay constraints to the Cloud
        #if FAILURE == self.checkSLADelayWithInCloud(sla):
        #    LOG_DEBUG("SLA (%s) cannot be placed in the Cloud. " % sla.identifier)
        #    return

        # Retrieve Cloud Hypervisor IP and sockfd
        hypIPAddr = self.m_dpid_to_hyp_ip[CLOUD_DPID]
        cloudSockfd = ""
        for pair in self.m_hyp_ip_sockfd_pair:
            if hypIPAddr == pair.val1[0]:
                cloudSockfd = pair.val2
                break

        # Sanity Check
        if cloudSockfd == "":
            LOG_DEBUG("Incorrect Placement to Cloud Hypervisor(%s) or System communication with Hypervisor(%s) is broken." % (CLOUD_DPID, CLOUD_DPID))
            return FAILURE

        # Again, Initializing some Data-structures
        sla.pathOfServiceChain = []
        sla.VNFsNetworkDpid    = []
        sla.VNFsNetworkMac     = []
        toBeInstalledVNFInfo   = []

        for index in range(0, len(sla.vnfInputList)):

            slaType   = sla.vnfInputList[index]
            cpuMemReq = sla.vnfCPUMemReq[index]

            # 'C1' (Static Constraint)  : Constraint for CPU Memory Status
            if cpuMemReq > (self.m_hypervisorMemStats[CLOUD_DPID]['capacity'] - self.m_hypervisorMemStats[CLOUD_DPID]['used']):
                LOG_DEBUG("SLA (%s) cannot be placed in the Cloud.(Test bed constraints)" % sla.identifier)
                return

            toBeInstalledVNFInfo.append(self.assignVNFResources(sla, index, CLOUD_DPID, False))
            sla.pathOfServiceChain.append(CLOUD_DPID)
            sla.VNFsNetworkDpid.append(CLOUD_DPID)

            # Hardcoded VLAN Start Tag to distinguish between SLAs
            sla.vlanCommonTag = 0x1000 | (sla.identifier << 8)

        # Note : No concept of Delay Buffer at the Cloud, SLA once placed at the cloud would not be brought back at the Edge-Fog layers

        # Note the complete path of the SLA in the network for all Hosts in the SLA
        sla.compPathOfSLA = self.generatePathOfSLA(sla, True)

        # Rest Operations to be performed when all the VNFs have started
        # Ref : placementToCloud_SLARestOp
        # Step 3: Save current context
        for newVNFInfo in toBeInstalledVNFInfo:

            # Sanity Check
            if newVNFInfo.macAddr in self.m_vnfOperationsOnStart:
                LOG_ERROR("This scenario should not occur. Programming Error!!!")
                return

            self.m_vnfOperationsOnStart[newVNFInfo.macAddr]                = {}
            self.m_vnfOperationsOnStart[newVNFInfo.macAddr]['new_vnfId']   = newVNFInfo.identifier
            self.m_vnfOperationsOnStart[newVNFInfo.macAddr]['scenario']    = "placement"

        sla.placementTimeData['vnfInstallStart'] = time.time()

        # Step 4: Install VNFs at their assigned Hypervisor's
        if FAILURE == self.installVNFsAtHypervisors(sla, toBeInstalledVNFInfo):
            LOG_ERROR("SLA (%s) cannot be placed in the Current Network. System issue!!!" % (sla.identifier))

            # Recover assigned Resources
            for vnfInfo in toBeInstalledVNFInfo:
                self.recoverVNFResources(sla, vnfInfo)
                
            return

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

    # Retreives the complete Path of the SLA via the Cloud
    def retreivePathOfSLAInCloud(self, sla):

        allPaths = {}

        # Forward Path
        for src_mac in sla.endUsersMac:
            for dst_mac in sla.endUsersMac:

                # Sanity Check
                if src_mac == dst_mac:
                    continue

                path = []

                src_dpid = self.m_mac_to_dpid_port[src_mac].val1
                dst_dpid = self.m_mac_to_dpid_port[dst_mac].val1

                flowpath_src_to_cloud = self.getSrcToDestPath(src_dpid, CLOUD_DPID)

                # -1 indicates an End-Point
                path = [[flowpath_src_to_cloud[0], -1]] # Source Hypervisor

                # Intermediate Switches between {Src Host to Cloud} 
                if len(flowpath_src_to_cloud) > 2:
                    for index in range(1, len(flowpath_src_to_cloud) - 1):
                        path.append([flowpath_src_to_cloud[index], 0])

                # Path of the Service Chain
                path.append([CLOUD_DPID, len(sla.vnfInputList)])

                flowpath_cloud_to_dst = self.getSrcToDestPath(CLOUD_DPID, dst_dpid)
                
                # Intermediate Switches between {Last VNF and Dst}
                if len(flowpath_cloud_to_dst) > 2:
                    for index in range(1, len(flowpath_cloud_to_dst) - 1):
                        path.append([flowpath_cloud_to_dst[index], 0])

                # -1 indicates an End-Point
                path.append([flowpath_cloud_to_dst[-1], -1]) # Destination Hypervisor

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
                LOG_INFO("SLA Complete Forward Path (Src %s to Dst %s) : %s"  % (src_dpid, dst_dpid, path))

        # Reverse Path
        for src_mac in sla.endUsersMac:
            for dst_mac in sla.endUsersMac:

                # Sanity Check
                if src_mac == dst_mac:
                    continue

                allPaths[src_mac][dst_mac]['prevRevPath'] = []
                allPaths[src_mac][dst_mac]['currRevPath'] = allPaths[dst_mac][src_mac]['currPath']

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
                        LOG_DEVEL("Datapath : %s | Match : vlan_vid-%s in_port-%s eth_src-%s eth_dst-%s | Pop VLAN |SetFeild : eth_dst - %s, Output : out_port-%s" % (this_dpid, sla.vlanCommonTag | processed_vnf_cnt, in_port, src_mac, dst_mac, vnf_mac, vnf_out_port))

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

                        LOG_DEVEL("Datapath : %s | Match : in_port-%s eth_src-%s eth_dst-%s | Push VLAN | SetFeild : vlan_tag-%s, eth_src - %s, Output : out_port-%s" % (this_dpid, vnf_out_port, vnf_mac, dst_mac, sla.vlanCommonTag | processed_vnf_cnt, src_mac, out_port))

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
                    LOG_DEVEL("Datapath : %s | Match : in_port-%s eth_src-%s eth_dst-%s | Push VLAN | SetFeild : vlan_tag-%s eth_src - %s, Output : out_port-%s" % (this_dpid, in_port, last_vnf_mac, dst_mac, sla.vlanCommonTag | processed_vnf_cnt, src_mac, out_port))

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
            LOG_DEVEL("Datapath : %s | Match : vlan_tag-%s in_port-%s eth_dst-%s | Pop VLAN | Output : out_port-%s" % (dst_dpid, sla.vlanCommonTag | processed_vnf_cnt, in_port, dst_mac, out_port))

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
            LOG_DEVEL("Datapath : %s | Match : in_port-%s eth_src-%s eth_dst-%s | Push VLAN | Output : vlan_vid-%s out_port-%s" % (src_dpid, pkt_in_port, src_mac, dst_mac, sla.vlanCommonTag, out_port))

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
        isForwardFirstVNFOfDpid  = True

        while True:
            
            ### Actions
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
                vnf_mac      = oldVNFsNetworkMac[processed_vnf_cnt]
                vnf_out_port = self.m_mac_to_dpid_port[vnf_mac].val2
                vnf_out_port = ofproto.OFPP_IN_PORT if vnf_out_port == in_port else vnf_out_port
            
                # If multiple VNFs at same Hypervisor
                if isMultipleVNFsAtSameDpid > 0:
                    # Do nothing, Packet sent in previous iteration
                    LOG_DEVEL("Handling Multiple Consecutive VNFs at the Same Hypervisor %s" % this_dpid)

                    if isForwardFirstVNFOfDpid:
                        match   = parser.OFPMatch(vlan_vid=(sla.vlanCommonTag | processed_vnf_cnt), in_port=in_port, eth_src=src_mac, eth_dst=dst_mac)
                        self.del_flow(datapath, priority, match)
                        LOG_DEVEL("Removed Datapath: %s | Match : in_port-%s eth_src-%s eth_dst-%s | SetFeild : eth_src - %s eth_dst - %s, Output : out_port-%s" % (this_dpid, in_port, src_mac, dst_mac, self.m_ovs_mac[this_dpid], vnf_mac, vnf_out_port))
                        isForwardFirstVNFOfDpid = False

                elif this_dpid != prev_switch:
                    # Check VLAN Tag
                    match = parser.OFPMatch(vlan_vid=(sla.vlanCommonTag | processed_vnf_cnt),in_port=in_port,eth_src=src_mac,eth_dst=dst_mac)
                    self.del_flow(datapath, priority, match)
                    LOG_DEVEL("Removed Datapath: %s | Match : vlan_vid-%s in_port-%s eth_src-%s eth_dst-%s | SetFeild : eth_src - %s, eth_dst - %s, Output : out_port-%s" % (this_dpid, sla.vlanCommonTag | processed_vnf_cnt, in_port, src_mac, dst_mac, self.m_ovs_mac[this_dpid], vnf_mac, vnf_out_port))

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

            if isMultipleVNFsAtSameDpid < 1:
                slaIndex                 += 1
                isMultipleVNFsAtSameDpid = path[slaIndex][1] - 1
                isForwardFirstVNFOfDpid  = True
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

        # Sanity Check
        if src == dst:
            return [src, dst]

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

        links = []

        # Consider Network edges for Cloud 
        if src == CLOUD_DPID or dst == CLOUD_DPID:
            cloudLinks = {}

            for dpid,data in self.m_graph['edges'].items():
                cloudLinks[dpid] = set()

                for nbr_dpid,port in data.items():
                    cloudLinks[dpid].add(nbr_dpid)

            links = cloudLinks

        # Consider Spanning Tree Links for Edge-Fog Network and
        else:
            links = self.m_spTreeLinks

        while queue:
            u = queue.popleft()
            color[u] = COLOR_BLACK

            #for v, port in self.m_graph['edges'][u].items():
            for v in links[u]:

                # TODO : Improve by using weights among the edges
                # Boils down to simple BFS
                if color[v] == COLOR_WHITE:
                    parent[v] = u
                    if v == dst:
                        path.append(v)
                        while parent[v] != -1:
                            v = parent[v]
                            path.append(v)
                        return list(reversed(path))
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
            seen = []
            seen.append(current)
            
            while current != dctEndPoints[endPoint]['parent'][current]:

                pathToCentre[endPoint].append(current)

                if current == -1: # Invalid Parent
                    LOG_ERROR("This scenario should not occur. Programming Error!!!")
                    break

                current = dctEndPoints[endPoint]['parent'][current]
                if current in seen:
                    LOG_ERROR("Programming Error")
                seen.append(current)

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
            # Spanning Tree with Cloud
            self._calculate_SpanningTreeWithCloud(datapath.id)

            # Spanning Tree without Cloud
            if datapath.id != CLOUD_DPID:
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

        # Remove Hypervisor CPU Utilization Stats
        if dpid in self.m_hypervisorCpuUtilStats:
            del self.m_hypervisorCpuUtilStats[dpid]

        # Remove Hypervisor VNF Status 
        if dpid in self.m_hypVNFStatus:
            del self.m_hypVNFStatus[dpid]

        # Update network's Spanning Tree
        for datapath in self.m_graph['switches']:
            # Spanning Tree with Cloud
            self._calculate_SpanningTreeWithCloud(datapath.id)

            # Spanning Tree without Cloud
            if datapath.id != CLOUD_DPID:
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

        if mac in self.m_vnfOperationsOnStart:
            LOG_INFO("VNF added @ dpid - %s : %s via port - %s" % (dpid, mac, port))
        else:
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

        # If Context is maintained
        if mac in self.m_vnfOperationsOnStart:

            # Retreive VNF Context
            newVNFId   = self.m_vnfOperationsOnStart[mac]['new_vnfId']
            newVNFInfo = gUsedVNFIds[newVNFId]

            # Complete rest of the Placement actions
            if self.m_vnfOperationsOnStart[mac]['scenario'] == "placement":
                self.placementOfSLA_RestOp(newVNFInfo)

            # Complete rest of the SLA Migration to Cloud actions
            elif self.m_vnfOperationsOnStart[mac]['scenario'] == "migrationToCloud" and newVNFInfo.slaIdentifier in self.m_SLACloudOperationsOnStart:
                self.migrateToCloud_RestOp(newVNFInfo, self.m_SLACloudOperationsOnStart[newVNFInfo.slaIdentifier])

            # Multi Migration of VNFs of the SLA to Nbr Hypervisor
            elif self.m_vnfOperationsOnStart[mac]['scenario'] == "multiMigration" and newVNFInfo.slaIdentifier in self.m_SLAMultiMigrationOpOnStart:
                self.migrateMultiVNFs_RestOp(self.m_SLAMultiMigrationOpOnStart[newVNFInfo.slaIdentifier], newVNFInfo.dpid)

            # Complete rest of the VNF Migration actions
            else:
                self.migrateVNF_RestOp(self.m_vnfOperationsOnStart[mac], dpid)

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
            # Spanning Tree with Cloud
            self._calculate_SpanningTreeWithCloud(datapath.id)

            # Spanning Tree without Cloud
            if datapath.id != CLOUD_DPID:
                self._calculate_SpanningTree(datapath.id)
                break

        # Initialize Link Nbrs
        self.mapLinkNbrs()

    # Updates the controller's view of switches in network topology, including Cloud
    def _calculate_SpanningTreeWithCloud(self, src):
        self.m_cloudLinks  = {}
        queue = deque()
        color = {}

        for node in self.m_graph['switches']:
            self.m_cloudLinks[node.id] = set()
            color[node.id] = COLOR_WHITE

        queue.append(src)

        while queue:
            u = queue.popleft()
            color[u] = COLOR_BLACK
            for v,port in self.m_graph['edges'][u].items():

                # TODO : Improve by using weights among the edges
                # Boils down to simple BFS
                if color[v] == COLOR_WHITE:
                    self.m_cloudLinks[v].add(u)
                    self.m_cloudLinks[u].add(v)
                    color[v] = COLOR_BLACK
                    queue.append(v)

    # Updates the controller's view of switches in network topology, excluding Cloud
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
                if v != CLOUD_DPID and color[v] == COLOR_WHITE:
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
    def generatePriorityScore(self, vnfInfoList, dpid, nbr_dpid):

        # Get linked SLA
        sla = self.m_SLAs[vnfInfoList[0].slaIdentifier]
        delayBuffer = sla.delayBuffer

        #pdb.set_trace()

        #### Parameter - 1: Link Latency between Current and Nbr
        if dpid > nbr_dpid:
            linkLatency = self.m_linkLatencyStats[dpid][nbr_dpid]['data']
            maxLatency  = self.m_linkLatencyStats[dpid][nbr_dpid]['max']
        else:
            linkLatency = self.m_linkLatencyStats[nbr_dpid][dpid]['data']
            maxLatency  = self.m_linkLatencyStats[nbr_dpid][dpid]['max']

        # TODO: Improve based on the existing Path of the Service Chain
        # Case 1 : Along the path of the Service Chain

        # Case 2 : Addition in the path


        #### Parameter - 2: VNF's CPU Mem Requirement
        cpuMemReq = 0
        for vnfInfo in vnfInfoList:
            cpuMemReq += vnfInfo.cpuMemReq
        cpuMemUnused = self.m_hypervisorMemStats[nbr_dpid]['capacity'] - self.m_hypervisorMemStats[nbr_dpid]['used']
        cpuMemCap    = self.m_hypervisorMemStats[nbr_dpid]['capacity']

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
        paramLinkBandwidthUnused = LINK_BW_LIMIT - linkBandwidthUsed

        if linkBandwidthReq > paramLinkBandwidthUnused:
            return [], FAILURE

        #### Parameter - 4: Preference to Neighbor already having a VNF of this SLA
        preferenceValue = 0
        preferenceIncrement = 0.5

        prevIndex = sla.VNFIds.index(vnfInfoList[0].identifier) - 1
        if prevIndex > -1:
        
            while prevIndex != -1:
                if prevIndex > 0 and sla.VNFIds[prevIndex] in self.m_hypVNFStatus[nbr_dpid]:
                    preferenceValue += preferenceIncrement

                prevIndex -= 1

        nextIndex = sla.VNFIds.index(vnfInfoList[-1].identifier) + 1
        if nextIndex < len(sla.VNFIds):
            while nextIndex < len(sla.VNFIds):

                if nextIndex > 0 and sla.VNFIds[nextIndex] in self.m_hypVNFStatus[nbr_dpid]:
                    preferenceValue += preferenceIncrement

                nextIndex += 1

        paramLinkBWNormalized      = float(float(paramLinkBandwidthUnused)/float(LINK_BW_LIMIT))
        paramCpuMemNormalized      = float(float(paramCpuMemRemain)/float(cpuMemCap))
        paramLinkLatencyNormalized = float(float(linkLatency)/float(maxLatency))

        # ppscore
        #LOG_INFO("|%s|%s|%s|" % (paramCpuMemNormalized, paramLinkBWNormalized, paramLinkLatencyNormalized))
        priorityScore = (alpha * paramCpuMemNormalized) + (beta * paramLinkBWNormalized) - (gamma * paramLinkLatencyNormalized) + preferenceValue

        return priorityScore,SUCCESS

    # Updates New SlA Rules for a particular Direction of Service Chain
    def updateNewSLARulesDirection(self, sla, src_mac, dst_mac, path, VNFsNetworkDpid, VNFsNetworkMac):

        priority = sla.compPathOfSLA[src_mac][dst_mac]['priority']

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
        isForwardFirstVNFOfDpid  = True

        while True:

            ### Actions
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
                vnf_mac      = VNFsNetworkMac[processed_vnf_cnt]
                vnf_out_port = self.m_mac_to_dpid_port[vnf_mac].val2
                vnf_out_port = ofproto.OFPP_IN_PORT if vnf_out_port == in_port else vnf_out_port
            
                # If multiple VNFs at same Hypervisor
                if isMultipleVNFsAtSameDpid > 0:
                    # Do nothing, Packet sent in previous iteration
                    LOG_DEVEL("Handling Multiple Consecutive VNFs at the Same Hypervisor %s" % this_dpid)

                    if isForwardFirstVNFOfDpid:
                        match   = parser.OFPMatch(vlan_vid=(sla.vlanCommonTag | processed_vnf_cnt), in_port=in_port, eth_src=src_mac, eth_dst=dst_mac)
                        actions = [parser.OFPActionPopVlan(0x8100),
                                   parser.OFPActionSetField(eth_src=self.m_ovs_mac[this_dpid]),
                                   parser.OFPActionSetField(eth_dst=vnf_mac),
                                   parser.OFPActionOutput(vnf_out_port)]

                        self.add_flow(datapath, priority, match, actions)
                        LOG_DEVEL("Datapath: %s | Match : in_port-%s eth_src-%s eth_dst-%s | Pop VLAN | SetFeild : eth_src - %s eth_dst - %s, Output : out_port-%s" % (this_dpid, in_port, src_mac, dst_mac, self.m_ovs_mac[this_dpid], vnf_mac, vnf_out_port))
                        isForwardFirstVNFOfDpid = False

                elif this_dpid != prev_switch:
                    # Check VLAN Tag
                    match   = parser.OFPMatch(vlan_vid=(sla.vlanCommonTag | processed_vnf_cnt),in_port=in_port,eth_src=src_mac,eth_dst=dst_mac)
                    actions = [parser.OFPActionPopVlan(0x8100),
                               parser.OFPActionSetField(eth_src=self.m_ovs_mac[this_dpid]),
                               parser.OFPActionSetField(eth_dst=vnf_mac),
                               parser.OFPActionOutput(vnf_out_port)]

                    self.add_flow(datapath, priority, match, actions)
                    LOG_DEVEL("Datapath: %s | Match : vlan_vid-%s in_port-%s eth_src-%s eth_dst-%s | Pop VLAN | SetFeild : eth_src - %s, eth_dst - %s, Output : out_port-%s" % (this_dpid, sla.vlanCommonTag | processed_vnf_cnt, in_port, src_mac, dst_mac, self.m_ovs_mac[this_dpid], vnf_mac, vnf_out_port))
               
                processed_vnf_cnt += 1
                prev_switch = this_dpid

                # Packet receiving from Last VNF
                # Scenario Handled in next Section.
                # All VNF(s) have been processed
                if processed_vnf_cnt == len(VNFsNetworkDpid):
                    break
                
                ### Reactions
                # Re-direct the packet received from the VNF through the Service Chain/Destination
                match = parser.OFPMatch(in_port=vnf_out_port, eth_src=vnf_mac, eth_dst=dst_mac)

                # Next VNF at the same Hypervisor
                if this_dpid == next_switch:
                    out_port     = ofproto.OFPP_IN_PORT
                    next_vnf_mac = VNFsNetworkMac[processed_vnf_cnt]
                    actions      = [parser.OFPActionSetField(eth_src=self.m_ovs_mac[this_dpid]),
                                    parser.OFPActionSetField(eth_dst=next_vnf_mac),
                                    parser.OFPActionOutput(out_port)]

                    LOG_DEVEL("Datapath: %s | Match : in_port-%s eth_src-%s eth_dst-%s | SetFeild : eth_src-%s, eth_dst-%s Output : out_port-%s" % (this_dpid, vnf_out_port, vnf_mac, dst_mac, self.m_ovs_mac[this_dpid], next_vnf_mac, out_port))

                else:
                    # Add VLAN Tag for processing in next Switch(s)
                    out_port = self.m_graph['edges'][this_dpid][next_switch]
                    actions  = [parser.OFPActionPushVlan(0x8100),
                                parser.OFPActionSetField(vlan_vid=(sla.vlanCommonTag | processed_vnf_cnt)),
                                parser.OFPActionSetField(eth_src=src_mac),
                                parser.OFPActionOutput(out_port)]

                    LOG_DEVEL("Datapath: %s | Match : in_port-%s eth_src-%s eth_dst-%s | Push VLAN | SetFeild : vlan_tag-%s, eth_src - %s, Output : out_port-%s" % (this_dpid, vnf_out_port, vnf_mac, dst_mac, sla.vlanCommonTag | processed_vnf_cnt, src_mac, out_port))

                self.add_flow(datapath, priority, match, actions)

            # Intermediate Switches
            else:
                match   = parser.OFPMatch(vlan_vid=(sla.vlanCommonTag | processed_vnf_cnt),in_port=in_port,eth_src=src_mac,eth_dst=dst_mac)
                actions = [parser.OFPActionOutput(out_port)]
                self.add_flow(datapath, priority, match, actions)
                LOG_DEVEL("Datapath: %s | Match : vlan_tag-%s in_port-%s eth_src-%s eth_dst-%s | Output : out_port-%s" % (this_dpid, sla.vlanCommonTag | processed_vnf_cnt, in_port, src_mac, dst_mac, out_port))

                prev_switch = this_dpid

            if isMultipleVNFsAtSameDpid < 1:
                slaIndex                 += 1
                isMultipleVNFsAtSameDpid = path[slaIndex][1] - 1
                isForwardFirstVNFOfDpid  = True
            else:
                isMultipleVNFsAtSameDpid -= 1

        ## 3. Actor - Last VNF and Intermediate Switches
        # Re-direct the packet from Last VNF to the Egress Point (Actual Dest. Point)
        last_vnf_mac  = VNFsNetworkMac[-1]
        last_vnf_dpid = VNFsNetworkDpid[-1]

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
                    LOG_DEVEL("Datapath: %s | Match : in_port-%s eth_src-%s eth_dst-%s | Push VLAN | SetFeild : vlan_tag-%s eth_src - %s, Output : out_port-%s" % (this_dpid, in_port, last_vnf_mac, dst_mac, sla.vlanCommonTag | processed_vnf_cnt, src_mac, out_port))

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
            LOG_DEVEL("Datapath: %s | Match : vlan_tag-%s in_port-%s eth_dst-%s | Pop VLAN | Output : out_port-%s" % (dst_dpid, sla.vlanCommonTag | processed_vnf_cnt, in_port, dst_mac, out_port))

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

            #if src_in_port == out_port:
            #    return

            self.add_flow(datapath, priority, match, actions) # Flow-Mod
            LOG_DEVEL("Datapath: %s | Match : in_port-%s eth_src-%s eth_dst-%s | Push VLAN | Output : vlan_vid-%s out_port-%s" % (src_dpid, src_in_port, src_mac, dst_mac, sla.vlanCommonTag, out_port))

    # Updates new SLA Flow Rules
    def updateNewSLAFlowRules(self, sla):

        src_mac = sla.endUsersMac[0]
        dst_mac = sla.endUsersMac[1]

        # Sanity Check
        if (src_mac not in sla.compPathOfSLA and dst_mac not in sla.compPathOfSLA[src_mac]) or (dst_mac not in sla.compPathOfSLA and src_mac not in sla.compPathOfSLA[dst_mac]):
            LOG_ERROR("This scenario should not occur. Programming Error!!!")
            return

        # Forward Path
        path = sla.compPathOfSLA[src_mac][dst_mac]['currPath']
        LOG_DEVEL("SLA(%s) Install Flow Rules between %s -> %s for Path: %s|%s|%s|" % (sla.identifier, src_mac, dst_mac, path, sla.VNFsNetworkDpid, sla.VNFsNetworkMac))
        self.updateNewSLARulesDirection(sla, src_mac, dst_mac, path, sla.VNFsNetworkDpid, sla.VNFsNetworkMac)
        
        # Reverse Path
        VNFsNetworkDpid = copy.deepcopy(sla.VNFsNetworkDpid)
        VNFsNetworkMac  = copy.deepcopy(sla.VNFsNetworkMac)
        VNFsNetworkDpid.reverse()
        VNFsNetworkMac.reverse()

        path = sla.compPathOfSLA[src_mac][dst_mac]['currRevPath']
        LOG_DEVEL("SLA(%s) Install Flow Rules between %s -> %s for Path: %s|%s|%s|" % (sla.identifier, dst_mac, src_mac, path, VNFsNetworkDpid, VNFsNetworkMac))
        self.updateNewSLARulesDirection(sla, dst_mac, src_mac, path, VNFsNetworkDpid, VNFsNetworkMac)

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
    
    def updateCompPathOfSLA(self, sla):

        for src_mac in sla.endUsersMac:
            for dst_mac in sla.endUsersMac:

                # Sanity Check
                if src_mac == dst_mac:
                    continue

                src_dpid = self.m_mac_to_dpid_port[src_mac].val1
                dst_dpid = self.m_mac_to_dpid_port[dst_mac].val1

                # Forward Path of Service Chain
                sla.compPathOfSLA[src_mac][dst_mac]['prevPath'] = copy.deepcopy(sla.compPathOfSLA[src_mac][dst_mac]['currPath'])
                path = copy.deepcopy(sla.compPathOfSLA[src_mac][dst_mac]['currPath'])
                path = []

                sla.compPathOfSLA[src_mac][dst_mac]['priority'] += 1

                # Add Src Dpid
                path.append([src_dpid, -1])

                # Src To 1st VNF
                src_to_vnf_path = self.getSrcToDestPath(src_dpid, sla.VNFsNetworkDpid[0])

                if len(src_to_vnf_path) > 2:
                    for inner_index in range(1, len(src_to_vnf_path) - 1):
                        inner_dpid = src_to_vnf_path[inner_index]
                        path.append([inner_dpid, 0])

                # Intermediate VNFs
                for index in range(0, len(sla.VNFsNetworkDpid)-1):
                    flow_path = self.getSrcToDestPath(sla.VNFsNetworkDpid[index], sla.VNFsNetworkDpid[index+1])
                    path.append([flow_path[0], 1]) # Src Dpid
                    # Skip Dst Dpid, gets added in next iteration
                    for inner_index in range(1, len(flow_path)-1):
                        inner_dpid = flow_path[inner_index]
                        path.append([inner_dpid, 0])

                # Add the Last VNF Dpid
                path.append([sla.VNFsNetworkDpid[-1], 1])

                # Last VNF to Dst
                dst_to_vnf_path = self.getSrcToDestPath(sla.VNFsNetworkDpid[-1], dst_dpid)
                for inner_index in range(1, len(dst_to_vnf_path)-1):
                        inner_dpid = dst_to_vnf_path[inner_index]
                        path.append([inner_dpid, 0])

                # Add Dst Dpid
                path.append([dst_dpid, -1])

                # Club duplicate entries, if exists
                path = self.mergeDuplicateEntries(path)

                sla.compPathOfSLA[src_mac][dst_mac]['currPath'] = copy.deepcopy(path)

                LOG_DEVEL("For Hosts %s -> %s: " % (src_mac, dst_mac))
                LOG_DEVEL("Previous Path: %s" % sla.compPathOfSLA[src_mac][dst_mac]['prevPath'])
                LOG_DEVEL("Current  Path: %s" % sla.compPathOfSLA[src_mac][dst_mac]['currPath'])

                # Reverse Path of Service Chain
                sla.compPathOfSLA[src_mac][dst_mac]['prevRevPath'] = copy.deepcopy(sla.compPathOfSLA[src_mac][dst_mac]['currRevPath'])
                path = copy.deepcopy(sla.compPathOfSLA[src_mac][dst_mac]['currRevPath'])
                path = []

                sla.compPathOfSLA[src_mac][dst_mac]['priority'] += 1

                VNFsNetworkDpid = copy.deepcopy(sla.VNFsNetworkDpid)
                VNFsNetworkDpid.reverse()

                temp_dpid = src_dpid
                src_dpid  = dst_dpid
                dst_dpid  = temp_dpid

                # Add Src Dpid
                path.append([src_dpid, -1])

                # Src To 1st VNF
                src_to_vnf_path = self.getSrcToDestPath(src_dpid, VNFsNetworkDpid[0])

                if len(src_to_vnf_path) > 2:
                    for inner_index in range(1, len(src_to_vnf_path) - 1):
                        inner_dpid = src_to_vnf_path[inner_index]
                        path.append([inner_dpid, 0])

                # Intermediate VNFs
                for index in range(0, len(VNFsNetworkDpid)-1):
                    flow_path = self.getSrcToDestPath(VNFsNetworkDpid[index], VNFsNetworkDpid[index+1])
                    path.append([flow_path[0], 1]) # Src Dpid
                    # Skip Dst Dpid, gets added in next iteration
                    for inner_index in range(1, len(flow_path)-1):
                        inner_dpid = flow_path[inner_index]
                        path.append([inner_dpid, 0])

                # Add the Last VNF Dpid
                path.append([VNFsNetworkDpid[-1], 1])

                # Last VNF to Dst
                dst_to_vnf_path = self.getSrcToDestPath(VNFsNetworkDpid[-1], dst_dpid)
                for inner_index in range(1, len(dst_to_vnf_path)-1):
                        inner_dpid = dst_to_vnf_path[inner_index]
                        path.append([inner_dpid, 0])

                # Add Dst Dpid
                path.append([dst_dpid, -1])

                # Club duplicate entries, if exists
                path = self.mergeDuplicateEntries(path)

                sla.compPathOfSLA[src_mac][dst_mac]['currRevPath'] = copy.deepcopy(path)

                LOG_DEVEL("For Hosts %s -> %s: " % (src_mac, dst_mac))
                LOG_DEVEL("Previous Rev Path: %s" % sla.compPathOfSLA[src_mac][dst_mac]['prevRevPath'])
                LOG_DEVEL("Current  Rev Path: %s" % sla.compPathOfSLA[src_mac][dst_mac]['currRevPath'])


    # Handles migration of Multiple VNFs from Current Hypervisor to Nbr Hypervisor
    # Scope : Completes all other operations for Migration
    def migrateMultiVNFs_RestOp(self, savedContext, new_dpid):
        global gBottlenecks

        savedContext['VNFRemCount'] -= 1

        # Install Flow Rules after all VNFs in the Cloud have started
        if savedContext['VNFRemCount'] != 0:
            return

        flowRulesInstallStartTime = time.time() * 1000 # In Milliseconds

        oldVNFsNetworkMacs = copy.deepcopy(savedContext['VNFsMac'])
        oldVNFsNetworkDpid = copy.deepcopy(savedContext['VNFsDpid'])
        oldVNFIds          = copy.deepcopy(savedContext['VNFsId'])
        startIndex         = copy.deepcopy(savedContext['startIndex'])
        bottleneckId       = copy.deepcopy(savedContext['bottleneckId'])

        old_dpid          = gUsedVNFIds[oldVNFIds[startIndex]].dpid
        sla               = self.m_SLAs[gUsedVNFIds[oldVNFIds[0]].slaIdentifier]

        # Update Complete Path of SLA
        self.updateCompPathOfSLA(sla)

        for index in range(startIndex, len(sla.VNFIds)):

            vnfId    = sla.VNFIds[index]
            vnfInfo  = gUsedVNFIds[vnfId]
            new_dpid = vnfInfo.dpid
        
            # Map VNFInfo to New Hypervisor
            self.m_hypVNFStatus[vnfInfo.dpid].append(vnfInfo.identifier)
            self.m_hypervisorMemStats[new_dpid]['used'] += vnfInfo.cpuMemReq 

        ## Step 4 : Add New flow rules for this change with Higher Priority
        self.updateNewSLAFlowRules(sla)
        LOG_DEVEL("Installed New SLA Flow Rules for the SLA: %s" % sla.identifier)

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

        for index in range(startIndex, len(oldVNFIds)):
            oldVNFId   = oldVNFIds[index]
            oldVNFInfo = gUsedVNFIds[oldVNFId]
            oldDpid    = oldVNFInfo.dpid

            # Stops VNF at the Old Hypervisor
            self.sendStopVNFCommand(oldVNFInfo, oldSockfd)

            ## Step 6: Remove Previous Flow Rules for all paths
            for src_mac in sla.endUsersMac:
                for dst_mac in sla.endUsersMac:

                    # Sanity Check
                    if src_mac == dst_mac:
                            continue

                    if sla.compPathOfSLA[src_mac][dst_mac]['prevPath'] != []:

                        self.removeOldSLAFlowRules(sla, src_mac, dst_mac, sla.compPathOfSLA[src_mac][dst_mac]['prevPath'], oldVNFsNetworkDpid, oldVNFsNetworkMacs)
                        sla.compPathOfSLA[src_mac][dst_mac]['prevPath'] = []

            ## Step 7: Update VNF Information w.r.t. Old Dpid in all related data-structures
            del self.m_mac_to_dpid_port[oldVNFInfo.macAddr]
            del self.m_dpid_to_mac_port[oldDpid][oldVNFInfo.macAddr]
            self.m_hypVNFStatus[oldDpid].remove(oldVNFInfo.identifier)
            self.m_hypervisorMemStats[oldDpid]['used'] -= oldVNFInfo.cpuMemReq

        # Remove entry
        del self.m_SLAMultiMigrationOpOnStart[sla.identifier]

        LOG_INFO("Successful VNF Migration of SLA (%s) from Hypervisor(%s) to Hypervisor(%s)" % (sla.identifier, old_dpid, new_dpid))
        LOG_INFO("The VNFs of SLA (%s) are placed at Hypervisors (%s) having VNF Ids (%s)" % ((sla.identifier, sla.VNFsNetworkDpid, sla.VNFIds)))
        if bottleneckId in gBottlenecks:
            LOG_INFO("Successfully handled Node Bottleneck at Hypervisor(%s)." % (gBottlenecks[bottleneckId]['dpid']))
        
            ## Step 8: Log Bottleneck Information
            self.logBottleneckInfo(bottleneckId, gBottlenecks[bottleneckId]['startTime'], 
                                   gBottlenecks[bottleneckId]['vnfInstallTime'], flowRulesInstallStartTime)
        
    # Handles migration of VNF from Current Hypervisor to Nbr Hypervisor
    # Scope : Completes all other operations for Migration
    def migrateVNF_RestOp(self, savedContext, new_dpid):
        global gBottlenecks

        flowRulesInstallStartTime = time.time() * 1000 # In Milliseconds

        old_dpid     = savedContext['old_dpid']
        old_mac      = savedContext['old_mac']
        old_vnfId    = savedContext['old_vnfId']
        new_vnfId    = savedContext['new_vnfId']

        oldVNFInfo  = gUsedVNFIds[old_vnfId]
        newVNFInfo  = gUsedVNFIds[new_vnfId]
        
        vnfIndexOfServiceChain = newVNFInfo.servChainIndex
        sla = self.m_SLAs[oldVNFInfo.slaIdentifier]

        # Maintain old information for Removing Flow Rules
        oldVNFsNetworkDpid = copy.deepcopy(sla.VNFsNetworkDpid)
        oldVNFsNetworkMac  = copy.deepcopy(sla.VNFsNetworkMac)
        oldVNFsNetworkMac[vnfIndexOfServiceChain] = old_mac

        ## Step 3: Update VNF Information w.r.t. New Dpid in all related data-structures
        newVNFInfo.dpid                             = new_dpid
        sla.VNFsNetworkDpid[vnfIndexOfServiceChain] = new_dpid

        # Update Complete Path of SLA
        self.updateCompPathOfSLA(sla)

        # Map VNFInfo to New Hypervisor
        self.m_hypVNFStatus[newVNFInfo.dpid].append(newVNFInfo.identifier)
        self.m_hypervisorMemStats[new_dpid]['used'] += newVNFInfo.cpuMemReq
        self.m_hypervisorMemStats[old_dpid]['used'] -= newVNFInfo.cpuMemReq

        ## Step 4 : Add New flow rules for this change with Higher Priority
        self.updateNewSLAFlowRules(sla)
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

        # Step 8: Maintain Bottleneck related Information
        bottleneckId = savedContext['bottleneckId']
        gBottlenecks[bottleneckId]['VNFRemCount'] -= 1

        # All VNFs related to the migration are up, bottleneck handled properly
        if gBottlenecks[bottleneckId]['VNFRemCount'] == 0:
            # Log Bottleneck Information
            LOG_INFO("Successfully handled Node Bottleneck at Hypervisor(%s) via Case %s" % (gBottlenecks[bottleneckId]['dpid'], gBottlenecks[bottleneckId]['situation']))
            LOG_INFO("The VNFs of SLA (%s) are placed at Hypervisors (%s) having VNF Ids (%s)" % ((sla.identifier, sla.VNFsNetworkDpid, sla.VNFIds)))
            self.logBottleneckInfo(bottleneckId, gBottlenecks[bottleneckId]['startTime'], 
                                   gBottlenecks[bottleneckId]['vnfInstallTime'], 
                                   flowRulesInstallStartTime)
            
    # Updates the Complete Path of SLA for all pairs of Hosts w.r.t. Cloud
    def updateCompPathOfSLAInCloud(self, sla):

        for src_mac in sla.endUsersMac:
            for dst_mac in sla.endUsersMac:

                # Sanity Check
                if src_mac == dst_mac:
                    continue

                sla.compPathOfSLA[src_mac][dst_mac]['prevPath']    = copy.deepcopy(sla.compPathOfSLA[src_mac][dst_mac]['currPath'])
                path = sla.compPathOfSLA[src_mac][dst_mac]['currPath']

                new_path = []

                # Source Dpid
                new_path.append(path[0]) 

                # Path from Source to Cloud
                src_to_cloud = self.getSrcToDestPath(path[0][0], CLOUD_DPID)
                for index in range(1, len(src_to_cloud) - 1):
                    new_path.append([src_to_cloud[index], 0])

                # Service Chain
                new_path.append([CLOUD_DPID, len(sla.vnfInputList)])  

                # Path from Cloud to Destination
                dst_to_cloud = self.getSrcToDestPath(CLOUD_DPID, path[-1][0])
                for index in range(1, len(dst_to_cloud) - 1):
                    new_path.append([dst_to_cloud[index], 0])
                
                # Dst Dpid
                new_path.append(path[-1])

                sla.compPathOfSLA[src_mac][dst_mac]['currPath'] = copy.deepcopy(new_path)

                LOG_DEVEL("For Hosts %s -> %s: " % (src_mac, dst_mac))
                LOG_DEVEL("Previous Path: %s" % sla.compPathOfSLA[src_mac][dst_mac]['prevPath'])
                LOG_DEVEL("Current  Path: %s" % sla.compPathOfSLA[src_mac][dst_mac]['currPath'])

        for src_mac in sla.endUsersMac:
            for dst_mac in sla.endUsersMac:

                # Sanity Check
                if src_mac == dst_mac:
                    continue

                sla.compPathOfSLA[src_mac][dst_mac]['prevRevPath'] = copy.deepcopy(sla.compPathOfSLA[src_mac][dst_mac]['currRevPath'])
                sla.compPathOfSLA[src_mac][dst_mac]['currRevPath'] = sla.compPathOfSLA[dst_mac][src_mac]['currPath']

                LOG_DEVEL("For Hosts %s -> %s: " % (src_mac, dst_mac))
                LOG_DEVEL("Previous Rev Path: %s" % sla.compPathOfSLA[src_mac][dst_mac]['prevRevPath'])
                LOG_DEVEL("Current  Rev Path: %s" % sla.compPathOfSLA[src_mac][dst_mac]['currRevPath'])


    def getPossibleMigrationOptions(self, dpid):
        slasInstalled = {}

        # Step 1: Seprate VNFs based on their SLAs
        for vnfId in self.m_hypVNFStatus[dpid]:
            vnfInfo        = gUsedVNFIds[vnfId]
            slaId          = vnfInfo.slaIdentifier
            servChainIndex = vnfInfo.servChainIndex

            if slaId not in slasInstalled:
                slasInstalled[slaId] = []

            slasInstalled[slaId].append(vnfInfo)

        # Step 2: Order the VNFs as per their Service Chain
        for slaId in slasInstalled:
            slasInstalled[slaId].sort(key=lambda x: x.servChainIndex)

        return slasInstalled

    # Handles migration of VNF from Current Hypervisor to Nbr Hypervisor
    # Scope limited to Updating Complete Paths and starting VNF at Nbr Hypervisor
    def migrateMultiVNFs_StartOp(self, dpid, nbr_dpid, vnfInfoList, bottleneckId):
        global gBottlenecks

        sla = self.m_SLAs[vnfInfoList[0].slaIdentifier]
        
        # Retrieve New Hypervisor IP and sockfd
        hypIPAddr = self.m_dpid_to_hyp_ip[nbr_dpid]
        newSockfd = ""

        for pair in self.m_hyp_ip_sockfd_pair:
            if hypIPAddr == pair.val1[0]:
                newSockfd = pair.val2
                break

        # Sanity Check
        if newSockfd == "":
            LOG_DEBUG("Incorrect Migration at Hypervisor (%s) or System communication with Hypervisor(%s) is broken." % (nbr_dpid, nbr_dpid))
            return FAILURE

        # Move all VNFs of the SLA
        for index in range(0, len(vnfInfoList)):
            oldVNFInfo = copy.deepcopy(vnfInfoList[index])

            # Rest of the Actions to be taken after VNF comes up at the New Hypervisor
            # Ref: migrateMultiVNFs_RestOp

            ## Step 1 : Save current context
            if sla.identifier not in self.m_SLAMultiMigrationOpOnStart:
                self.m_SLAMultiMigrationOpOnStart[sla.identifier]                 = {}
                self.m_SLAMultiMigrationOpOnStart[sla.identifier]['VNFsMac']      = copy.deepcopy(sla.VNFsNetworkMac)
                self.m_SLAMultiMigrationOpOnStart[sla.identifier]['VNFsDpid']     = copy.deepcopy(sla.VNFsNetworkDpid)
                self.m_SLAMultiMigrationOpOnStart[sla.identifier]['VNFRemCount']  = len(vnfInfoList)
                self.m_SLAMultiMigrationOpOnStart[sla.identifier]['VNFsId']       = copy.deepcopy(sla.VNFIds)
                self.m_SLAMultiMigrationOpOnStart[sla.identifier]['startIndex']   = oldVNFInfo.servChainIndex
                self.m_SLAMultiMigrationOpOnStart[sla.identifier]['bottleneckId'] = bottleneckId


            newVNFInfo = self.assignVNFResources(sla, oldVNFInfo.servChainIndex, nbr_dpid, True)

            self.m_vnfOperationsOnStart[newVNFInfo.macAddr]              = {}
            self.m_vnfOperationsOnStart[newVNFInfo.macAddr]['old_dpid']  = dpid
            self.m_vnfOperationsOnStart[newVNFInfo.macAddr]['old_mac']   = oldVNFInfo.macAddr
            self.m_vnfOperationsOnStart[newVNFInfo.macAddr]['old_vnfId'] = oldVNFInfo.identifier
            self.m_vnfOperationsOnStart[newVNFInfo.macAddr]['new_vnfId'] = newVNFInfo.identifier
            self.m_vnfOperationsOnStart[newVNFInfo.macAddr]['scenario']  = "multiMigration"


            # Maintain context for the new VNF for this Bottleneck
            gBottlenecks[bottleneckId]['VNFRemCount'] += 1
            if gBottlenecks[bottleneckId]['vnfInstallTime'] == 0.0:
                gBottlenecks[bottleneckId]['vnfInstallTime'] = time.time() * 1000 # In Milliseconds

            ## Step 2a : Start VNF at the Nbr Hypervisor with same configuration
            # Starts VNF at the Hypervisor
            self.sendStartVNFCommand(newVNFInfo, newSockfd)

            ## Step 2b : Forwarding Msg Command
            self.sendForwardingVNFCommand(sla, newVNFInfo, newSockfd, newVNFInfo.servChainIndex)

    # Handles migration of VNF from Current Hypervisor to Nbr Hypervisor
    # Scope limited to Updating Complete Paths and starting VNF at Nbr Hypervisor
    def migrateVNF_StartOp(self, dpid, new_dpid, vnfId, bottleneckId):
        global gBottlenecks

        oldVNFInfo = gUsedVNFIds[vnfId]

        vnfIndexOfServiceChain = oldVNFInfo.servChainIndex
        sla = self.m_SLAs[oldVNFInfo.slaIdentifier]

        newVNFInfo = self.assignVNFResources(sla, oldVNFInfo.servChainIndex, new_dpid, True)

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
            LOG_DEBUG("Incorrect Migration at Hypervisor (%s) or System communication with Hypervisor(%s) is broken." % (new_dpid, new_dpid))
            return FAILURE

        # Rest of the Actions to be taken after VNF comes up at the New Hypervisor
        # Ref: migrateVNF_RestOp

        ## Step 1 :  Save current context
        # Sanity Check
        if newVNFInfo.macAddr in self.m_vnfOperationsOnStart:
            LOG_ERROR("This scenario should not occur. Highly impossible!!!")
            return

        self.m_vnfOperationsOnStart[newVNFInfo.macAddr]                 = {}
        self.m_vnfOperationsOnStart[newVNFInfo.macAddr]['old_dpid']     = old_dpid
        self.m_vnfOperationsOnStart[newVNFInfo.macAddr]['old_mac']      = oldVNFInfo.macAddr
        self.m_vnfOperationsOnStart[newVNFInfo.macAddr]['old_vnfId']    = oldVNFInfo.identifier
        self.m_vnfOperationsOnStart[newVNFInfo.macAddr]['new_vnfId']    = newVNFInfo.identifier
        self.m_vnfOperationsOnStart[newVNFInfo.macAddr]['scenario']     = "migration"
        self.m_vnfOperationsOnStart[newVNFInfo.macAddr]['bottleneckId'] = bottleneckId

        # Maintain context for the new VNF for this Bottleneck
        gBottlenecks[bottleneckId]['VNFRemCount'] += 1
        if gBottlenecks[bottleneckId]['vnfInstallTime'] == 0.0:
            gBottlenecks[bottleneckId]['vnfInstallTime'] = time.time() * 1000 # In Milliseconds

        ## Step 2a : Start VNF at the Nbr Hypervisor with same configuration
        # Starts VNF at the Hypervisor
        self.sendStartVNFCommand(newVNFInfo, newSockfd)

        ## Step 2b : Forwarding Msg Command
        self.sendForwardingVNFCommand(sla, newVNFInfo, newSockfd, newVNFInfo.servChainIndex)

    # Handle Node Bottleneck
    def handleNodeBottleneck(self, dpid):
        global gBottlenecks, gBottleneckCount

        currentTime = time.time() * 1000 # In Milliseconds

        # Maintain information about Node Bottleneck
        gBottleneckCount += 1
        bottleneckId = gBottleneckCount
        gBottlenecks[bottleneckId]                   = {}
        gBottlenecks[bottleneckId]['startTime']      = currentTime
        gBottlenecks[bottleneckId]['vnfInstallTime'] = float(0.0)
        gBottlenecks[bottleneckId]['dpid']           = dpid
        gBottlenecks[bottleneckId]['endTime']        = float(0.0)
        gBottlenecks[bottleneckId]['VNFRemCount']    = 0
        gBottlenecks[bottleneckId]['situation']      = 0

        priorityScores = {}

        # All VNFs installed at the Bottlenecked Hypervisor are considered
        possibleSLAOptions = self.getPossibleMigrationOptions(dpid)

        for slaId in possibleSLAOptions:
            for index in reversed(range(0, len(possibleSLAOptions[slaId]))):

                # Consider all Nbrs of this dpid
                # Retrieve Nbrs of the current Dpid
                for nbr_dpid,out_port in self.m_graph['edges'][dpid].items():

                    if nbr_dpid == CLOUD_DPID or nbr_dpid in self.m_SLAs[slaId].endPointsDpid:
                        continue

                    vnfInfoList = []
                    for choice in range(index, len(possibleSLAOptions[slaId])):
                        vnfInfoList.append(possibleSLAOptions[slaId][choice])
                        
                    score,result = self.generatePriorityScore(vnfInfoList, dpid, nbr_dpid)
                    
                    #yyy
                    if result == SUCCESS:
                        key = "%s|%s" % (slaId, nbr_dpid)
                        priorityScores[key] = make_tuple(vnfInfoList, score)

        maxPriorityScore = 0.0
        maxPSKey = ""
        for key in priorityScores:
            slaId    = key.strip().split('|')[0]
            nbr_dpid = key.strip().split('|')[1]

            vnfIds = []
            for vnfInfo in priorityScores[key].val1:
                vnfIds.append(vnfInfo.identifier)

            if priorityScores[key].val2 > maxPriorityScore:
                maxPriorityScore = priorityScores[key].val2
                maxPSKey = key
        
        # Movement to the Nbrs not possible, leads to Case 2
        if maxPriorityScore == 0.0:
            
            if self.handleNodeBottleneckCase2(bottleneckId) == SUCCESS:
                LOG_INFO("Bottleneck handled at Hypervisor (%s) with Case 2." % dpid)    
            else:
                if self.handleNodeBottleneckCase3(bottleneckId) == FAILURE:
                    LOG_INFO("This scenario should not occur. Programming Error!!!")
            return

        slaId    = int(maxPSKey.strip().split('|')[0])
        nbr_dpid = int(maxPSKey.strip().split('|')[1])

        # Check if Multiple VNFs are moved
        if len(priorityScores[maxPSKey].val1) > 1:
            vnfIds = []
            for vnfInfo in priorityScores[maxPSKey].val1:
                vnfIds.append(vnfInfo.identifier)

            LOG_INFO("To Handle Node Bottleneck at Hypervisor(%s), VNFs(%s) are migrated to Hypervisor (%s)." % (dpid, vnfIds, nbr_dpid))

            gBottlenecks[bottleneckId]['situation'] = 4 # Multiple VNFs of SLA Migrated to Nbr

            # Handles migration of mutliple VNFs from Current Hypervisor to Nbr Hypervisor
            self.migrateMultiVNFs_StartOp(dpid, nbr_dpid, priorityScores[maxPSKey].val1, bottleneckId)

        else:
            gBottlenecks[bottleneckId]['situation'] = 1

            # Handles migration of VNF from Current Hypervisor to Nbr Hypervisor
            self.migrateVNF_StartOp(dpid, nbr_dpid, priorityScores[maxPSKey].val1[0].identifier, bottleneckId)

    # Handles migration of entire SLA (associated VNFs) to the Cloud
    # Scope limited to Updating Complete Paths and starting VNF at the Cloud
    def migrateToCloud_StartOp(self, sla, bottleneckId):
        global gBottlenecks

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
            # Ref: migrateToCloud_RestOp

            ## Step 1 : Save current context
            if sla.identifier not in self.m_SLACloudOperationsOnStart:
                self.m_SLACloudOperationsOnStart[sla.identifier]                 = {}
                self.m_SLACloudOperationsOnStart[sla.identifier]['VNFsMac']      = copy.deepcopy(sla.VNFsNetworkMac)
                self.m_SLACloudOperationsOnStart[sla.identifier]['VNFsDpid']     = copy.deepcopy(sla.VNFsNetworkDpid)
                self.m_SLACloudOperationsOnStart[sla.identifier]['VNFRemCount']  = len(sla.vnfInputList)
                self.m_SLACloudOperationsOnStart[sla.identifier]['VNFsId']       = copy.deepcopy(sla.VNFIds)
                self.m_SLACloudOperationsOnStart[sla.identifier]['bottleneckId'] = bottleneckId

            newVNFInfo = self.assignVNFResources(sla, index, CLOUD_DPID, True)

            self.m_vnfOperationsOnStart[newVNFInfo.macAddr]                 = {}
            self.m_vnfOperationsOnStart[newVNFInfo.macAddr]['old_dpid']     = old_dpid
            self.m_vnfOperationsOnStart[newVNFInfo.macAddr]['old_mac']      = oldVNFInfo.macAddr
            self.m_vnfOperationsOnStart[newVNFInfo.macAddr]['old_vnfId']    = oldVNFInfo.identifier
            self.m_vnfOperationsOnStart[newVNFInfo.macAddr]['new_vnfId']    = newVNFInfo.identifier
            self.m_vnfOperationsOnStart[newVNFInfo.macAddr]['scenario']     = "migrationToCloud"
            
            # Maintain context for the new VNF for this Bottleneck
            gBottlenecks[bottleneckId]['VNFRemCount'] += 1
            if gBottlenecks[bottleneckId]['vnfInstallTime'] == 0.0:
                gBottlenecks[bottleneckId]['vnfInstallTime'] = time.time() * 1000 # In Milliseconds

            ## Step 2a : Start VNF at the Nbr Hypervisor with same configuration
            # Starts VNF at the Hypervisor
            self.sendStartVNFCommand(newVNFInfo, cloudSockfd)

            ## Step 2b : Forwarding Msg Command
            self.sendForwardingVNFCommand(sla, newVNFInfo, cloudSockfd, index)

    # Handles remaining steps of migration of entire SLA (associated VNFs) to the Cloud
    # Scope : Completes all other operations for Migration
    def migrateToCloud_RestOp(self, newVNFInfo, savedContext):
        global gBottlenecks

        sla = self.m_SLAs[newVNFInfo.slaIdentifier]

        savedContext['VNFRemCount'] -= 1

        # Install Flow Rules after all VNFs in the Cloud have started
        if savedContext['VNFRemCount'] != 0:
            return

        flowRulesInstallStartTime = time.time() * 1000 # In Milliseconds

        oldVNFNetworkMacs = copy.deepcopy(savedContext['VNFsMac'])
        oldVNFNetworkDpid = copy.deepcopy(savedContext['VNFsDpid'])
        oldVNFIds         = copy.deepcopy(savedContext['VNFsId'])
        bottleneckId      = copy.deepcopy(savedContext['bottleneckId'])

        ## Step 2 : Update Complete Path of SLA
        self.updateCompPathOfSLAInCloud(sla)

        ## Step 3a: Update VNF Information w.r.t. New Dpid in all related data-structures
        for index in range(0, len(sla.VNFIds)):
            vnfId    = sla.VNFIds[index]
            vnfInfo  = gUsedVNFIds[vnfId]
            new_dpid = vnfInfo.dpid
        
            # Map VNFInfo to New Hypervisor
            self.m_hypVNFStatus[vnfInfo.dpid].append(vnfInfo.identifier)
            self.m_hypervisorMemStats[new_dpid]['used'] += vnfInfo.cpuMemReq 

        ## Step 4 : Add New flow rules for this change with Higher Priority
        self.updateNewSLAFlowRules(sla)
        LOG_DEBUG("Installed New SLA Flow Rules for the SLA (%s) moved to the Cloud." % sla.identifier)

        ## Step 5: Stop VNF at the old Hypervisor
        for index in range(0, len(oldVNFIds)):
            oldVNFId   = oldVNFIds[index]
            oldVNFInfo = gUsedVNFIds[oldVNFId]
            oldDpid    = oldVNFInfo.dpid
            
            hypIPAddr = self.m_dpid_to_hyp_ip[oldDpid]
            oldSockfd = ""
            for pair in self.m_hyp_ip_sockfd_pair:
                if hypIPAddr == pair.val1[0]:
                    oldSockfd = pair.val2
                    break

            # Sanity Check
            if oldSockfd == "":
                LOG_DEBUG("System communication with Old Hypervisor(%s) is broken. Migration Failed." % (oldDpid.dpid))
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

                        self.removeOldSLAFlowRules(sla, src_mac, dst_mac, sla.compPathOfSLA[src_mac][dst_mac]['prevPath'], oldVNFNetworkDpid, oldVNFNetworkMacs)
                        sla.compPathOfSLA[src_mac][dst_mac]['prevPath'] = []
        
            ## Step 7: Update VNF Information w.r.t. Old Dpid in all related data-structures
            del self.m_mac_to_dpid_port[oldVNFInfo.macAddr]
            del self.m_dpid_to_mac_port[oldDpid][oldVNFInfo.macAddr]
            self.m_hypVNFStatus[oldDpid].remove(oldVNFInfo.identifier)
            self.m_hypervisorMemStats[oldDpid]['used'] -= oldVNFInfo.cpuMemReq

        # Remove entry
        del self.m_SLACloudOperationsOnStart[newVNFInfo.slaIdentifier]

        # Yipee... SLA is properly migrated to the Cloud
        LOG_INFO("Successful Migration of SLA (%s) from Hypervisor(%s) to Cloud Hypervisor(%s)" % 
                 (sla.identifier, oldVNFNetworkDpid, CLOUD_DPID))

        LOG_INFO("Successfully handled Node Bottleneck at Hypervisor(%s) via Case %s" % 
                 (gBottlenecks[bottleneckId]['dpid'], gBottlenecks[bottleneckId]['situation']))

        ## Step 8: Log Bottleneck Information
        self.logBottleneckInfo(bottleneckId, gBottlenecks[bottleneckId]['startTime'], 
                               gBottlenecks[bottleneckId]['vnfInstallTime'], flowRulesInstallStartTime)

    # Logs Information about the Bottleneck
    def logBottleneckInfo(self, bottleneckId, startTime, vnfInstallStartTime, flowRulesInstallStartTime):
        global gBottlenecks
        endTime = time.time() * 1000 # In Milliseconds

        infos = []

        infos.append("\n")
        infos.append("SITUATION: %s" % gBottlenecks[bottleneckId]['situation'])
        infos.append("VNF-INSTALL-START-TIME : %s" % str(float(gBottlenecks[bottleneckId]['vnfInstallTime']) - float(gBottlenecks[bottleneckId]['startTime'])))
        infos.append("FLOW-RULES-INSTALL-START-TIME : %s" % str(float(flowRulesInstallStartTime) - float(gBottlenecks[bottleneckId]['startTime'])))
        infos.append("TOTAL-TIME: %s" % str(float(endTime) - float(gBottlenecks[bottleneckId]['startTime'])))

        for info in infos:
            self.write_to_file(LOG_BOTTLENECK_FILENAME, info, 'a')

        # Delete Bottleneck information
        del gBottlenecks[bottleneckId]

    # Moves a VNF to a Nbr by creating Rsrcs at his Nbr
    def handleNodeBottleneckCase2(self, bottleneckId):
        global gBottlenecks

        priorityScores = {}

        gBottlenecks[bottleneckId]['situation'] = 2
        dpid = gBottlenecks[bottleneckId]['dpid']

        # All VNFs installed at the Bottlenecked Hypervisor are considered
        possibleSLAOptions = self.getPossibleMigrationOptions(dpid)

        for slaId in possibleSLAOptions:
            for index in reversed(range(0, len(possibleSLAOptions[slaId]))):

                # Consider all Nbrs of this dpid
                # Retrieve Nbrs of the current Dpid
                for nbr_dpid,out_port in self.m_graph['edges'][dpid].items():

                    if nbr_dpid == CLOUD_DPID or nbr_dpid in self.m_SLAs[slaId].endPointsDpid:
                        continue

                    vnfInfoList1 = []
                    for choice in range(index, len(possibleSLAOptions[slaId])):
                        vnfInfoList1.append(possibleSLAOptions[slaId][choice])

                    score1,result1 = self.generatePriorityScore(vnfInfoList1, dpid, nbr_dpid)
                    vnfIds = []
                    for id in vnfInfoList1:
                        vnfIds.append(id.identifier)

                    if result1 == FAILURE:
                        continue

                    possibleSLAOptionsInner = self.getPossibleMigrationOptions(nbr_dpid)
                    for slaIdInner in possibleSLAOptionsInner:
                        for indexInner in reversed(range(0, len(possibleSLAOptionsInner[slaIdInner]))):

                            # Consider all Nbrs of this nbr_dpid
                            # Retrieve Nbrs of nbr_dpid
                            for nbr_nbrs_dpid,nbr_nbrs_out_port in self.m_graph['edges'][nbr_dpid].items():

                               # Do not consider the Cloud or the bottlenecked Hypervisor
                                if nbr_nbrs_dpid == CLOUD_DPID or nbr_nbrs_dpid == dpid or nbr_nbrs_dpid in self.m_SLAs[slaIdInner].endPointsDpid:
                                    continue

                                vnfInfoList2 = []
                                for choiceInner in range(indexInner, len(possibleSLAOptionsInner[slaIdInner])):
                                    vnfInfoList2.append(possibleSLAOptionsInner[slaIdInner][choiceInner])

                                    score2,result2 = self.generatePriorityScore(vnfInfoList2, nbr_dpid, nbr_nbrs_dpid)

                                    vnfIdsx = []
                                    for id in vnfInfoList2:
                                        vnfIdsx.append(id.identifier)

                                    #LOG_INFO("%s -> %s | %s" % (nbr_dpid, nbr_nbrs_dpid, vnfIdsx))

                                    if result2 == SUCCESS:
                                        #priorityScores[make_tuple(vnfIndex, nbr_dpid, nbr_vnfIndex, nbr_nbrs_dpid)] = score1 + score2
                                        LOG_INFO("SUCCESS: %s -> %s | %s & %s -> %s | %s" % (dpid, nbr_dpid, vnfIds, nbr_dpid, nbr_nbrs_dpid, vnfIdsx))
                                        
                                        key = "%s|%s|%s|%s" % (slaId, nbr_dpid, slaIdInner, nbr_nbrs_dpid)
                                        priorityScores[key] = make_tuple(vnfInfoList1, vnfInfoList2, score1 + score2)

        maxPriorityScore = 0.0
        maxPSKey         = []
        for key in priorityScores:
            if priorityScores[key].val3 > maxPriorityScore:
                maxPriorityScore = priorityScores[key].val3
                maxPSKey = key
        
        # If not possible to create Resources at 2-hop Nbr for migration
        if maxPriorityScore == 0.0:
            return FAILURE

        # w.r.t Migration from nbr_dpid to  nbr_nbrs_dpid
        # Check if Multiple VNFs are moved
        nbr_dpid      = int(maxPSKey.strip().split('|')[1])
        slaIdInner    = int(maxPSKey.strip().split('|')[2]) 
        nbr_nbrs_dpid = int(maxPSKey.strip().split('|')[3])

        if len(priorityScores[maxPSKey].val2) > 1:
            vnfIds = []
            for vnfInfo in priorityScores[maxPSKey].val2:
                vnfIds.append(vnfInfo.identifier)

            LOG_INFO("To Handle Node Bottleneck at Hypervisor(%s), VNFs(%s) are migrated from Hypervisor(%s) to Hypervisor (%s)." % (dpid, vnfIds, nbr_dpid, nbr_nbrs_dpid))

            gBottlenecks[bottleneckId]['situation'] = 4 # Multiple VNFs of SLA Migrated to Nbr

            # Handles migration of mutliple VNFs from Current Hypervisor to Nbr Hypervisor
            self.migrateMultiVNFs_StartOp(nbr_dpid, nbr_nbrs_dpid, priorityScores[maxPSKey].val2, bottleneckId)

        else:
            gBottlenecks[bottleneckId]['situation'] = 1

            # Handles migration of VNF from Current Hypervisor to Nbr Hypervisor
            self.migrateVNF_StartOp(nbr_dpid, nbr_nbrs_dpid, priorityScores[maxPSKey].val2[0].identifier, bottleneckId)


        # w.r.t Migration from dpid to nbr_dpid
        # Check if Multiple VNFs are moved
        slaId    = int(maxPSKey.strip().split('|')[0]) 
        nbr_dpid = int(maxPSKey.strip().split('|')[1])

        if len(priorityScores[maxPSKey].val1) > 1:
            vnfIds = []
            for vnfInfo in priorityScores[maxPSKey].val1:
                vnfIds.append(vnfInfo.identifier)

            LOG_INFO("To Handle Node Bottleneck at Hypervisor(%s), VNFs(%s) are migrated from Hypervisor(%s) to Hypervisor (%s)." % (dpid, vnfIds, dpid, nbr_dpid))

            gBottlenecks[bottleneckId]['situation'] = 4 # Multiple VNFs of SLA Migrated to Nbr

            # Handles migration of mutliple VNFs from Current Hypervisor to Nbr Hypervisor
            self.migrateMultiVNFs_StartOp(dpid, nbr_dpid, priorityScores[maxPSKey].val1, bottleneckId)

        else:
            gBottlenecks[bottleneckId]['situation'] = 1

            # Handles migration of VNF from Current Hypervisor to Nbr Hypervisor
            self.migrateVNF_StartOp(dpid, nbr_dpid, priorityScores[maxPSKey].val1[0].identifier, bottleneckId)

        return SUCCESS

    # Moves a VNF and its entire SLA Chain to the Cloud
    def handleNodeBottleneckCase3(self, bottleneckId):
        global gBottlenecks

        gBottlenecks[bottleneckId]['situation'] = 3
        dpid = gBottlenecks[bottleneckId]['dpid']

        # All VNFs installed at the Bottlenecked Hypervisor
        # Randomly select a VNF and its associated SLA as Victim
        vnfIndex = random.randint(0,len(self.m_hypVNFStatus[dpid])-1)
        vnfId    = self.m_hypVNFStatus[dpid][vnfIndex]
        vnfInfo  = gUsedVNFIds[vnfId]
        sla = self.m_SLAs[vnfInfo.slaIdentifier]
        LOG_INFO("Hypervisor (%s) : SLA (%s) considered for Migration to Cloud (Case 3)." % (dpid, vnfInfo.identifier))

        # Migrate the selected SLA to the Cloud
        self.migrateToCloud_StartOp(sla, bottleneckId)

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
            words       = line.split()
            dpid        = int(words[0])
            ipAddr      = words[1].strip()
            memCapacity = int(words[2].strip('\n'))

            dpid_ip_pair[dpid] = ipAddr

            # Initialize CPU Memory Stats
            # Assuming, a Hypervisor is connected to only one OVS-switch
            if dpid not in self.m_hypervisorMemStats:
                self.m_hypervisorMemStats[dpid] = {}
                self.m_hypervisorMemStats[dpid]['capacity'] = memCapacity
                self.m_hypervisorMemStats[dpid]['used']     = 0

        return dpid_ip_pair

def LOG_INFO(string):
    print str(string) + " - " + str(currentframe().f_back.f_lineno)

def LOG_DEBUG(string):
    print str(string) + " - " + str(currentframe().f_back.f_lineno)

def LOG_DEVEL(string):
    print str(string) + " - " + str(currentframe().f_back.f_lineno)
    return

def LOG_ERROR(string):
    print str(string) + " - " + str(currentframe().f_back.f_lineno)

class make_tuple():

    def __init__(self, value1, value2, value3=None, value4=None):
        self.val1 = value1
        self.val2 = value2
        self.val3 = value3
        self.val4 = value4
