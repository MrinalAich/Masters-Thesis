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
#, custom_payload
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
import pdb, time, random, json

from matplotlib import pyplot as plt
from matplotlib import animation
from ryu.ofproto import ether
from ryu.lib.packet import arp, packet

from ryu.lib.packet import ipv4, icmp, tcp,arp
from ryu.ofproto import ether
from ryu.ofproto import inet
from collections import namedtuple
Payload = namedtuple('Payload', 'pathId timeSent')

# Macro definations
RECV_BUFFER = 4096
OPERATOR_API_SOCK_PORT = 12345
IP_ADDR = "127.0.0.1"
CPU_STATS_SERVER_PORT = 1234

SUCCESS = 1
FAILURE = 0

LOGGING_DEBUG = False
LOGGING_INFO  = 0

COLOR_WHITE = 0
COLOR_BLACK = 1

High_Priority = 65530

UNIT_OF_BANDWIDTH = 1
throughput_anim_fileName = "throughput.json"
latency_anim_fileName    = "latency.json"
cpu_anim_fileName        = "cpu.json"

linkLatencyEthType   = 0x07c3
switchLatencyEthType = 0x07c4

# Thresholds
hypervisorCPULimit = 100
hypervisorCPUThreshold = 0.90

linkBWLimit = 100000 # 100 Kbps
linkBWThreshold = 0.95

# Timeout till the SLA agrrement starts coming
SLA_INPUT_TIMEOUT = 12

# Structure of a SLA aggrement
class struct_SLA(object):
     def __init__(self, identifier, vnfList, delayTolerated, reqBW, reqCPU, endUsersMac, endPointsDpid):
        self.identifier         = identifier
        self.isInstalled        = False          # Whether SLA is installed
        self.vnfList            = vnfList        # VNF Types
        self.delayTolerated     = delayTolerated # ms
        self.reqBW              = reqBW          # Mbps
        self.reqCPU             = reqCPU         # Mbps
        self.endUsersMac        = endUsersMac    # End-Users
        self.endPointsDpid      = endPointsDpid  # End-Points DPID
        self.delayBufer         = -1             # Delay-buffer
        self.VNFsNetworkMac     = []
        self.VNFsNetworkDpid    = []
        self.centre             = -1
        self.pathToCentre       = {}
        self.pathOfServiceChain = []

class Orchestrator(app_manager.RyuApp):
    OFP_VERSIONS = [ofproto_v1_3.OFP_VERSION]

    def __init__(self, *args, **kwargs):
        super(Orchestrator, self).__init__(*args, **kwargs)
        # Monitor
        self.DM_createMonitorThreads()

        self.mac_to_port = {}

        # Orchestrator
        self.orchestratorMsgQueue = ""
        self.DO_createOrchestratorThread()

        # API
        self.DAPI_adminThread()

        # Locks
        # TODO: self.of_mutexLock = Lock()      # Mutex Locks for OpenFlow parameters

        # Flow Manager 
        self.m_graph = {}                       # Graph data structure
        self.m_graph.setdefault('edges', {})
        self.m_graph.setdefault('switches', set())
        self.m_graph.setdefault('hosts', {})    # Hosts connected to the Switch
        
        # Monitor
        self.m_switchFlowStats      = {}
        self.m_switchLatencyStats   = {}
        self.m_linkLatencyStats     = {}
        self.m_hypervisorCpuStats   = {}

        # Variables related to CPU stats collection
        self.server_socket = ""
        self.cpu_stats_Socket_List = []

        self.monitor_latency_dst_mac = "11:00:00:00:00:00"
        self.monitor_latency_src_mac = "22:00:00:00:00:00"

        self.m_spTreeLinks = {}

        self.m_mac_to_dpid_port = {}
        self.m_dpid_to_mac_port = {}

        self.m_dpid_to_vnf = {}
        self.m_vnfs        = {}  

        self.m_topology_api_app = self

        self.debugFlag = True
        
        self.m_SLAsCount = 0
        self.m_SLAs = []          # Maintains all the SLAs

        self.m_endUsersToSLA = {} # Reverse Map

        '''
        # Hardcoded SLA agreement
        sla_object = struct_SLA(self.m_SLAsCount, ['Firewall'], 10, 100, 10, ['00:00:00:00:00:11', '00:00:00:00:00:31'], [1,3])
        sla_object.isInstalled = True

        self.m_SLAs.append(sla_object)
        self.m_SLAsCount = self.m_SLAsCount + 1

        # Creates reverse Map of EndPoints to SLAs
        self.mapEndUsersToSLAs(sla_object)
        '''

    # Monitor Thread
    def _monitorLink_SwitchStatsThread(self):

        while True:
            # Flow Stats from Switch
            for dp in self.m_graph['switches']:
                self.DM_request_stats(dp)

            hub.sleep(1)
            
            # Switch Latency
            for dpid in self.m_graph['switches']:
                identifier = int(dpid.id)
                #pdb.set_trace()
                timestamp  = float('%.2f' % time.time())
                datapath   = self.getDatapath(dpid.id)

                # Initialize Switch-Latency Monitoring
                if dpid.id not in self.m_switchLatencyStats:
                    self.m_switchLatencyStats[dpid.id] = float(0.0)

                self.send_packet(switchLatencyEthType, dpid.id, datapath.ofproto.OFPP_CONTROLLER, identifier, timestamp)

            # Link Latency
            for dpid in self.m_graph['edges']:
                for nbr_dpid,out_port in self.m_graph['edges'][dpid].items():
                    # Initialize Link monitoring
                    if dpid > nbr_dpid:
                        if dpid not in self.m_linkLatencyStats:
                            self.m_linkLatencyStats[dpid] = {}
                        
                        if nbr_dpid not in self.m_linkLatencyStats[dpid]:
                            self.m_linkLatencyStats[dpid][nbr_dpid] = {}
                        
                        # TODO: Assuming all single digit dpid's
                        identifier = int(str(dpid) + str(nbr_dpid))
                        timestamp  = float('%.2f' % time.time())
                        self.send_packet(linkLatencyEthType, dpid, out_port, identifier, timestamp)

            hub.sleep(1)

    # Function sends custom packet for Link monitoring
    # Ref: Monitoring Latency with Openflow 
    def send_packet(self, eth_type, current_dpid, out_port, identifier, timestamp):
    
        # Create a custom packet
        dst_mac = self.monitor_latency_dst_mac
        src_mac = self.monitor_latency_src_mac
        ethernet_type = eth_type

        ethernet_header = ethernet.ethernet(ethertype=ethernet_type, dst=dst_mac, src=src_mac)
        #payload = custom_payload.custom_payload(identifier=identifier, timestamp=timestamp)
        payload = Payload(identifier, timestamp)
        #ip_pck.set_payload(repr(pl))

        custom_packet = packet.Packet()
        custom_packet.add_protocol(ethernet_header)
        custom_packet.add_protocol(payload)
        custom_packet.serialize()

        custom_packet.data = str(custom_packet.data) + str(identifier) + str(timestamp)

        datapath = self.getDatapath(current_dpid)
        actions = [datapath.ofproto_parser.OFPActionOutput(port=out_port)]

        out = datapath.ofproto_parser.OFPPacketOut(datapath=datapath, buffer_id=0xffffffff, in_port=datapath.ofproto.OFPP_CONTROLLER, actions=actions, data=custom_packet.data)
        datapath.send_msg(out)

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

        # Hardcoded SLA agreement
        slaObject = struct_SLA(self.m_SLAsCount, ['Firewall'], 10, 100, 10, ['00:00:00:00:00:21', '00:00:00:00:00:31'], [2,3])
        self.m_SLAs.append(slaObject)
        self.m_SLAsCount = self.m_SLAsCount + 1

        # Creates reverse Map of EndPoints to SLAs
        self.mapEndUsersToSLAs(slaObject)

        # Algorithm-1. Placement of the SLA
        self.placementOfSLA(slaObject)

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
        self.server_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.server_socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.server_socket.bind((IP_ADDR, CPU_STATS_SERVER_PORT))
        self.server_socket.listen(10)
     
        # Add server socket object to the list of readable connections
        self.cpu_stats_Socket_List.append(self.server_socket)

        while 1:
            # get the list sockets which are ready to be read through select
            # 4th arg, time_out  = 0 : poll and never block
            ready_to_read,ready_to_write,in_error = select.select(self.cpu_stats_Socket_List,[],[],0)
          
            for sock in ready_to_read:
                # a new connection request recieved
                if sock == self.server_socket: 
                    sockfd, addr = self.server_socket.accept()
                    self.cpu_stats_Socket_List.append(sockfd)

                # a message from a client, not a new connection
                else:
                    try:
                        data = sock.recv(RECV_BUFFER)
                        if data:
                            # Function interprets the Docker stats
                            # information from a Hypervisor
                            self.processHypervisorCPUInfo(data)
                        
                        else:
                            # remove the socket that's broken
                            if sock in self.cpu_stats_Socket_List:
                                self.cpu_stats_Socket_List.remove(sock)
                    # exception 
                    except:
                        continue

        self.server_socket.close()

    # Updates Hypervisor's CPU Utilization by Docker Containers
    def processHypervisorCPUInfo(self, data):
        #global mutex

        data = data.split(":")
        hypervisorIP      = data[0]
        hypervisorRcdTime = float(data[1])
        cpu_usage         = data[2]

        if self.debugFlag:
            print "Hypervisor [%s] at %s | %s MB: " % (hypervisorIP, hypervisorRcdTime, data)

        # TODO Assuming Available CPU RAM 100 MB
        #mutex.acquire()

        if hypervisorIP not in self.m_hypervisorCpuStats:
            self.m_hypervisorCpuStats[hypervisorIP] = {}
        
        self.m_hypervisorCpuStats[hypervisorIP]['time']  = hypervisorRcdTime
        self.m_hypervisorCpuStats[hypervisorIP]['usage'] = cpu_usage

        #LOG_DEBUG("CPU Stat Update of %s @ %s -> %s" % (hypervisorIP, 
        #           self.m_hypervisorCpuStats[hypervisorIP]['time'],
        #           self.m_hypervisorCpuStats[hypervisorIP]['usage']))

        self.write_to_file(cpu_anim_fileName, self.m_hypervisorCpuStats)
        #mutex.release()

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
            LOG_DEBUG("This scenario should not occur. Programming Error!!!")

        # Initialize Port-Stats Monitoring
        if port not in self.m_switchFlowStats[dpid]:
            currentTime = float('%.2f' % time.time())
            self.m_switchFlowStats[dpid][port] = {}
            self.m_switchFlowStats[dpid][port]['startRecordedTime'] = currentTime
            self.m_switchFlowStats[dpid][port]['LastTotalBytes']    = rxBytes + txBytes
            self.m_switchFlowStats[dpid][port]['LastRecordedTime']  = currentTime
            self.m_switchFlowStats[dpid][port]['data'] = []

            '''
            # Initialize Switch-Latency Monitoring
            if dpid not in self.m_switchLatencyStats:
                self.m_switchLatencyStats[dpid] = float(0.0)
            '''

        else:
            # Update Port-Stats Monitoring
            currentTime = float('%.2f' % time.time())
            currentBytesProcessed = rxBytes + txBytes

            deltaBytesProcessed = abs(currentBytesProcessed - self.m_switchFlowStats[dpid][port]['LastTotalBytes'])
            deltaTime   = currentTime - self.m_switchFlowStats[dpid][port]['LastRecordedTime']
            
            durationFromStart = currentTime - self.m_switchFlowStats[dpid][port]['startRecordedTime']
            bandwidthAcheived = float(deltaBytesProcessed * 8)/float(float(UNIT_OF_BANDWIDTH) * float(deltaTime)) # Bytes/sec
            self.m_switchFlowStats[dpid][port]['data'] = [durationFromStart, bandwidthAcheived]

            self.m_switchFlowStats[dpid][port]['LastTotalBytes']   = currentBytesProcessed
            self.m_switchFlowStats[dpid][port]['LastRecordedTime'] = currentTime

            self.write_to_file(throughput_anim_fileName, self.m_switchFlowStats)
        
            '''
            # Update Switch-Latency Monitoring
            deltaLatencyTime = currentTime - self.m_switchFlowStats[dpid]['LastSentTime']
            self.m_switchLatencyStats[dpid] = float(deltaLatencyTime)/2 # One-way calculation
            '''

    # Functions updates Link Latency
    def DM_update_latency(self, ethernet_type, packet):
        return
        #pdb.set_trace()
        curr_time     = float('%.2f' % time.time())
        payload       = packet[1][46:]
        
        ### Link Latency
        if ethernet_type == linkLatencyEthType:
            iden          = str(payload[:2])
            sent_time     = float(payload[2:])
            total_latency = curr_time - sent_time
            (dpid1,dpid2) = (int(iden[0]),int(iden[1])) if int(iden[0]) > int(iden[1]) else (int(iden[1]),int(iden[0]))
            
            # Sanity Check
            if dpid1 not in self.m_linkLatencyStats or dpid2 not in self.m_linkLatencyStats[dpid1]:
                LOG_DEBUG("This scenario should not occur. Programming Error!!!")
                return

            # Initialization
            if 'startRecordedTime' not in self.m_linkLatencyStats[dpid1][dpid2]:
                self.m_linkLatencyStats[dpid1][dpid2]['startRecordedTime'] = curr_time

            durationFromStart = curr_time - self.m_linkLatencyStats[dpid1][dpid2]['startRecordedTime']

            if dpid1 not in self.m_switchLatencyStats or dpid2 not in self.m_switchLatencyStats:
                LOG_DEBUG("Switch Latency Module not initialized. Programming Error!!!")
                return

            dpid1_latency = self.m_switchLatencyStats[dpid1]
            dpid2_latency = self.m_switchLatencyStats[dpid2]
            link_latency = total_latency - dpid1_latency - dpid2_latency

            self.m_linkLatencyStats[dpid1][dpid2]['data'] = [durationFromStart, abs(link_latency)]

            if False:
                LOG_DEBUG("Switch Latency : %s -        %s seconds" % (dpid1, dpid1_latency))
                LOG_DEBUG("Switch Latency : %s -        %s seconds" % (dpid2, dpid2_latency))
                LOG_DEBUG("Round Latency  : %s <-> %s : %s seconds" % (dpid1, dpid2, total_latency))
                LOG_DEBUG("Latency over the link %s <---> %s :  %s seconds " % (dpid1, dpid2, link_latency))

            self.write_to_file(latency_anim_fileName, self.m_linkLatencyStats)

        ### Switch Latency
        elif ethernet_type == switchLatencyEthType:
            iden = str(payload[0])
            sent_time     = float(payload[1:])
            total_latency = curr_time - sent_time
            dpid = (int(iden))

            # Sanity Check
            if dpid not in self.m_switchLatencyStats:
                #pdb.set_trace()
                LOG_DEBUG("This scenario should not occur. Programming Error!!!")
                return

            deltaSwitchLatencyTime = curr_time - sent_time
            self.m_switchLatencyStats[dpid] = float(deltaSwitchLatencyTime/2)


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

        
        if eth.ethertype in [linkLatencyEthType,switchLatencyEthType]:
            self.DM_update_latency(eth.ethertype, pkt)
            return

        dst_mac = eth.dst
        src_mac = eth.src
        dpid = datapath.id

        if "00:00:00:00:00" not in src_mac and "00:00:00:00:00" not in dst_mac:
            return

        match = []
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

            sla_object = 0
            for sla_object in isUsersBelongToSLA:
                LOG_DEBUG("%s & %s belong to SLA : %s" % (src_mac, dst_mac, sla_object.identifier))
                break

            self.installSLAFlowRules(sla_object, src_mac, dst_mac, msg, ofproto, parser, in_port)

            LOG_DEBUG("Forwarding Current Packet.")
            # Retreive flow path from src to dst
            flowpath_src_to_dst = []
            flowpath_src_to_dst = self.get_flow_path(src_dpid, dst_dpid)
            flowpath_src_to_dst.reverse()

            LOG_DEBUG(" Path : From Src to Dst Switches : %s %s " % (src_dpid, dst_dpid))
            print_flowpath(flowpath_src_to_dst)

            # 1. Actor - Egress Switch
            datapath = self.getDatapath(dst_dpid)
            out_port = self.m_mac_to_dpid_port[dst_mac].val2
            match    = parser.OFPMatch(eth_dst=dst_mac)
            actions  = [parser.OFPActionOutput(out_port)]
            self.add_flow(datapath, High_Priority, match, actions)

            # SLACase 1: Host1 -- FW -- Host2
            '''
            fw_mac = "00:00:00:00:00:22"
            fw_dpid = 2
            '''

            # SLACase 2: FW -- Host1 -- Host2
            fw_mac = "00:00:00:00:00:12"
            fw_dpid = 1

            # 2. Actor - In-between Switches
            for i in range(1, len(flowpath_src_to_dst)-1):
                if flowpath_src_to_dst[i] == dst_dpid:
                    #pdb.set_trace()
                    break

                this_dpid   = flowpath_src_to_dst[i]
                datapath    = self.getDatapath(this_dpid)
                next_switch = flowpath_src_to_dst[i+1]
                out_port    = self.m_graph['edges'][this_dpid][next_switch]                

                if this_dpid == fw_dpid:

                    # Change dst_Mac to mac_address of FW
                    fw_out_port = self.m_mac_to_dpid_port[fw_mac].val2
                    match       = parser.OFPMatch(eth_src=src_mac, eth_dst=dst_mac)
                    actions     = [parser.OFPActionSetField(eth_dst=fw_mac),
                                parser.OFPActionOutput(fw_out_port)]
                    self.add_flow(datapath, High_Priority, match, actions)

                    # Re-direct the packet from FW towards the destination
                    out_port = self.m_graph['edges'][this_dpid][next_switch]
                    match    = parser.OFPMatch(in_port=fw_out_port, eth_src=fw_mac, eth_dst=dst_mac)
                    actions  = [parser.OFPActionSetField(eth_src=src_mac),
                                parser.OFPActionOutput(out_port)]
                    self.add_flow(datapath, High_Priority, match, actions)

                else:
                    match    = parser.OFPMatch(eth_dst=dst_mac)
                    actions  = [parser.OFPActionOutput(out_port)]
                    self.add_flow(datapath, High_Priority, match, actions)

            # 3. Actor - Ingress Switch (Packet-Out and Flow-Mod)
            datapath    = self.getDatapath(src_dpid)
            next_switch = flowpath_src_to_dst[1]
            out_port    = self.m_graph['edges'][src_dpid][next_switch]
            match       = parser.OFPMatch(eth_dst=dst_mac)
            actions     = [parser.OFPActionOutput(out_port)]
            self.add_flow(datapath, High_Priority, match, actions) # Flow-Mod
            data        = msg.data if msg.buffer_id == ofproto.OFP_NO_BUFFER else None
            out_msg     = datapath.ofproto_parser.OFPPacketOut(datapath=datapath, buffer_id=msg.buffer_id, in_port=in_port, actions=actions, data=data)
            datapath.send_msg(out_msg) # Packet-Out


        # Known Host - Install flow rules along the path
        else:

            # Retreive flow path from src to dst
            flowpath_src_to_dst = []
            flowpath_src_to_dst = self.get_flow_path(src_dpid, dst_dpid)
            flowpath_src_to_dst.reverse()

            LOG_DEBUG(" Path : From Src to Dst Switches : %s %s " % (src_dpid, dst_dpid))
            print_flowpath(flowpath_src_to_dst)

            # 1. Actor - Egress Switch
            datapath = self.getDatapath(dst_dpid)
            out_port = self.m_mac_to_dpid_port[dst_mac].val2
            match    = parser.OFPMatch(eth_dst=dst_mac)
            actions  = [parser.OFPActionOutput(out_port)]
            self.add_flow(datapath, High_Priority, match, actions)

            # 2. Actor - In-between Switches
            for i in range(1, len(flowpath_src_to_dst)-1):
                if flowpath_src_to_dst[i] == dst_dpid:
                    break
                this_dpid   = flowpath_src_to_dst[i]
                datapath    = self.getDatapath(this_dpid)
                next_switch = flowpath_src_to_dst[i+1]
                out_port    = self.m_graph['edges'][this_dpid][next_switch]
                match       = parser.OFPMatch(eth_dst=dst_mac)
                actions     = [parser.OFPActionOutput(out_port)]
                self.add_flow(datapath, High_Priority, match, actions)


            # 3. Actor - Ingress Switch (Packet-Out and Flow-Mod)
            datapath    = self.getDatapath(src_dpid)
            next_switch = flowpath_src_to_dst[1]
            out_port    = self.m_graph['edges'][src_dpid][next_switch] if src_dpid != dst_dpid else self.m_graph['hosts'][dst_dpid][dst_mac]
            actions     = [parser.OFPActionOutput(out_port)]
            match       = parser.OFPMatch(eth_dst=dst_mac)
            self.add_flow(datapath, High_Priority, match, actions) # Flow-Mod
            data        = msg.data if msg.buffer_id == ofproto.OFP_NO_BUFFER else None
            out_msg     = datapath.ofproto_parser.OFPPacketOut(datapath=datapath, buffer_id=msg.buffer_id, in_port=in_port, actions=actions, data=data)
            datapath.send_msg(out_msg) # Packet-Out


    # Actual Placement of SLA-defined Flow Rules
    def placementOfSLA(self, sla):

        LOG_DEBUG("Placement for SLA (%s) started." % sla.identifier)

        ## Step 1. Find Centre for this SLA to place
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
            dctEndPoints[endPoint]['parent']    = {}
            for datapath in self.m_graph['switches']:
                uVertex = datapath.id
                dctEndPoints[endPoint]['parent'][uVertex] = -1
            dctEndPoints[endPoint]['parent'][endPoint] = endPoint

        queueEndPoints = deque()
        for endDpid in sla.endPointsDpid:
            queueEndPoints.append(endDpid)

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

                        # Temporarily Disabled
                        '''
                        # C1 - Constraint for Edge's Latency/Delay

                        # Retreive Link latency
                        linkLatency = 0.0
                        if uVertex in self.m_linkLatencyStats and vVertex in self.m_linkLatencyStats[uVertex]:
                            linkLatency = self.m_linkLatencyStats[uVertex][vVertex]['data'][1]

                        elif vVertex in self.m_linkLatencyStats and uVertex in self.m_linkLatencyStats[vVertex]:
                            linkLatency = self.m_linkLatencyStats[vVertex][uVertex]['data'][1]

                        if delayFromEndPoint[uVertex][endPoint] + linkLatency <= sla.delayTolerated :
                            delayFromEndPoint[vVertex][endPoint] = delayFromEndPoint[uVertex][endPoint] + linkLatency

                        else:
                            continue
                        '''
                
                        '''
                        # C2 - Constraint for CPU utilization
                        hypervisorIP = "192.168.111." + str(vVertex) + "0" # TODO Hardcoded - Mapping from HypervisorIP to its dpid

                        if sla.reqCPU > hypervisorCPUThreshold * (hypervisorCPULimit - self.m_hypervisorCpuStats[hypervisorIP]['usage']):
                            continue
                        '''

                        # C3 - Constraint for Link's Available BW
                        uVertex_to_vVertexPort = self.m_graph['edges'][uVertex][vVertex]
                        linkBandwidthAchieved  = self.m_switchFlowStats[uVertex][uVertex_to_vVertexPort]['data'][1]

                        if sla.reqBW > linkBWThreshold * (linkBWLimit - linkBandwidthAchieved):
                            continue
                
                        dctEndPoints[endPoint]['visited'].add(vVertex)

                        # Add EndPoint to Seen DS
                        seenEndPoints[vVertex].append(endPoint)

                        # Update Parent Pointer
                        dctEndPoints[endPoint]['parent'][vVertex] = uVertex

                        # Push into the Queue 
                        dctEndPoints[endPoint]['queue'].append(vVertex)

                        # Check whether all End points are observed
                        # TODO : Handle this scenario
                        if vVertex != 2 and vVertex != 3 and len(seenEndPoints[vVertex]) == len(sla.endPointsDpid):

                            # Center Found - Eureka!!!
                            sla.centre = vVertex
                            dctEndPoints[endPoint]['queue'] = []
                            queueEndPoints = []
                            break

            if len(dctEndPoints[endPoint]['queue']):
                queueEndPoints.append(endPoint)

        pdb.set_trace()
        sla.pathToCentre = self.getPathFromCentreToAllEndPoints(sla, dctEndPoints)

        # Update Delay Buffer used for future migration purposes
        sla.delayBuffer = -1

        for item,val in delayFromEndPoint[vVertex].items():

            if val <= sla.delayTolerated:
                sla.delayBuffer = max(sla.delayBuffer, val)

        sla.delayBuffer = sla.delayTolerated - sla.delayBuffer

        if sla.delayBuffer == -1:
            LOG_DEBUG("This scenario should not occur. Programming Error!!!")
        else:
            LOG_DEBUG("SLA (%s) Placed at Hypervisor (%s) with Delay Buffer (%s)." % (sla.identifier, vVertex, sla.delayBuffer))
        
        # TODO 
        # Step 2. Map rest of the VNFs of the Service Chain


        # TODO : 
        # Step 3. Install VNF's of the SLA at their assigned Hypervisor's
        # As of Now : Assuming the VNF's is already installed.

        # TODO : Tweak
        if sla.identifier == 0:
            # SLACase 1:  Host1 -- FW -- Host2
            # Firewall's MAC
            '''
            sla.VNFsNetworkMac.append('00:00:00:00:00:22')
            sla.VNFsNetworkDpid.append(2)
            sla.pathOfServiceChain.append(2)
            '''

            # SLACase 2: FW -- Host1 -- Host2
            # Firewall's MAC
            sla.VNFsNetworkMac.append('00:00:00:00:00:12')
            sla.VNFsNetworkDpid.append(1)
            sla.pathOfServiceChain.append(1)

        # Step 4: Install the respective flow Rules will be done when
        # End-points intiates communication
        # Reference : installSLAFlowRules(sla)

        # For infomation purpose
        hypervisor_dpid = ""
        vnf_mac = ""
        for index in range(0, len(sla.VNFsNetworkMac)):
            hypervisor_dpid += str(sla.VNFsNetworkDpid[index]) + ","
            vnf_mac += str(sla.VNFsNetworkMac[index]) + ","

        # Yes Yes Yes... SLA is properly installed over the Network
        sla.isInstalled = True

        LOG_DEBUG("SLA (%s) is installed over the Network with the VNFs placed at"
                  " Hypervisors (%s) having MAC addresses (%s)." % 
                  (sla.identifier, hypervisor_dpid, vnf_mac))

    # Installs the Flow Rules w.r.t. SLA using Hard Timeout
    def installSLAFlowRules(self, sla, src_mac, dst_mac, msg, ofproto, parser, pkt_in_port):

        #pdb.set_trace()

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

                match       = parser.OFPMatch(in_port=in_port, eth_src=src_mac)
                actions     = [parser.OFPActionOutput(out_port)]
                self.add_flow(datapath, High_Priority, match, actions)

                prev_switch = this_dpid
    
        ## 2. Actor - All the VNFs of the Service Chain
        ## Packet moves from 1st VNF to the rest of the VNF(s), if any
        processed_vnf_cnt = 0
        flowpath_start_to_last = sla.pathOfServiceChain

        if len(flowpath_start_to_last):

            for i in range(0, len(flowpath_start_to_last)):

                this_dpid   = flowpath_start_to_last[i]
                datapath    = self.getDatapath(this_dpid)
                in_port     = self.m_graph['edges'][this_dpid][prev_switch] if this_dpid != prev_switch else pkt_in_port

                if i != len(flowpath_start_to_last)-1:
                    next_switch = flowpath_start_to_last[i+1]
                    out_port    = self.m_graph['edges'][this_dpid][next_switch]

                # If installed VNF's dpid
                if this_dpid == sla.VNFsNetworkDpid[processed_vnf_cnt]:

                    # Change dst_Mac to mac_address of the VNF
                    vnf_mac      = sla.VNFsNetworkMac[processed_vnf_cnt]
                    vnf_out_port = self.m_mac_to_dpid_port[vnf_mac].val2
                    match        = parser.OFPMatch(in_port=in_port,eth_src=src_mac)
                    actions      = [parser.OFPActionSetField(eth_dst=vnf_mac),
                                    parser.OFPActionOutput(vnf_out_port)]
                    self.add_flow(datapath, High_Priority, match, actions)

                    processed_vnf_cnt += 1
                   
                    # Packet receiving from Last VNF
                    # Scenario Handled in next Section.
                    if i == len(flowpath_start_to_last) - 1:
                        break

                    # Re-direct the packet from the VNF towards the destination
                    out_port = self.m_graph['edges'][this_dpid][next_switch]
                    match    = parser.OFPMatch(in_port=vnf_out_port, eth_src=vnf_mac, eth_dst=dst_mac)
                    actions  = [parser.OFPActionSetField(eth_src=src_mac),
                                parser.OFPActionOutput(out_port)]
                    self.add_flow(datapath, High_Priority, match, actions)

                # Intermediate Switches
                else:
                    match    = parser.OFPMatch(in_port=in_port,eth_src=src_mac)
                    actions  = [parser.OFPActionOutput(out_port)]
                    self.add_flow(datapath, High_Priority, match, actions)

                prev_switch = this_dpid
                
        ## 3. Actor - Last VNF and Intermediate Switches
        # Re-direct the packet from Last VNF to the Egress Point (Actual Dest. Point)
        last_vnf_mac  = sla.VNFsNetworkMac[processed_vnf_cnt-1]
        last_vnf_dpid = sla.VNFsNetworkDpid[processed_vnf_cnt-1]
        
        flowpath_last_to_dst = self.getSlaDestPath(sla, dst_mac) # TODO: To be discussed
        dst_dpid = self.m_mac_to_dpid_port[dst_mac].val1

        ## Case 3a. Destination VNF Hypervisor is also connected to the Egress Switch
        if len(flowpath_last_to_dst) == 1:

            # Re-direct the packet from the VNF towards the destination
            datapath  = self.getDatapath(dst_dpid)
            same_port = self.m_mac_to_dpid_port[dst_mac].val2
            match     = parser.OFPMatch(in_port=same_port, eth_src=last_vnf_mac, eth_dst=dst_mac)
            actions   = [parser.OFPActionSetField(eth_src=src_mac),
                        parser.OFPActionOutput(same_port)]
            self.add_flow(datapath, High_Priority, match, actions)

        else:
        ## Case 3b. Destination VNF Hypervisor and Egress Switch are not connected
            last_vnf_in_port = self.m_dpid_to_mac_port[last_vnf_dpid][last_vnf_mac]

            for i in range(0, len(flowpath_last_to_dst)-1):

                this_dpid   = flowpath_last_to_dst[i]
                datapath    = self.getDatapath(this_dpid)
                next_switch = flowpath_last_to_dst[i+1]
                out_port    = self.m_graph['edges'][this_dpid][next_switch]
                in_port     = last_vnf_in_port if i == 0 else self.m_graph['edges'][this_dpid][prev_switch]

                # Re-format the packet from the Last VNF towards the actual destination
                if this_dpid == last_vnf_dpid:
                    match   = parser.OFPMatch(in_port=in_port, eth_src=last_vnf_mac, eth_dst=dst_mac)
                    actions = [parser.OFPActionSetField(eth_src=src_mac),
                               parser.OFPActionOutput(out_port)]
                    self.add_flow(datapath, High_Priority, match, actions)

                # Intermediate Switches
                else:
                    match    = parser.OFPMatch(in_port=in_port, eth_dst=dst_mac)
                    actions  = [parser.OFPActionOutput(out_port)]
                    self.add_flow(datapath, High_Priority, match, actions)

                prev_switch = this_dpid
        
        ## Case 4. Actor - Egress Switch
            datapath = self.getDatapath(dst_dpid)
            in_port  = self.m_graph['edges'][dst_dpid][prev_switch]
            out_port = self.m_mac_to_dpid_port[dst_mac].val2
            match    = parser.OFPMatch(in_port=in_port ,eth_dst=dst_mac)
            actions  = [parser.OFPActionOutput(out_port)]
            self.add_flow(datapath, High_Priority, match, actions)

        ## 5. Actor - Ingress Switch
        # Case 5a. Ingrees Switch and Centre Switch are the same
        if len(flowpath_src_to_centre) != 1:

            datapath    = self.getDatapath(src_dpid)
            next_switch = flowpath_src_to_centre[1]
            out_port    = self.m_graph['edges'][src_dpid][next_switch]
            match       = parser.OFPMatch(in_port=pkt_in_port, eth_src=src_mac)
            actions     = [parser.OFPActionOutput(out_port)]
            self.add_flow(datapath, High_Priority, match, actions) # Flow-Mod

            data    = msg.data if msg.buffer_id == ofproto.OFP_NO_BUFFER else None
            out_msg = datapath.ofproto_parser.OFPPacketOut(datapath=datapath, buffer_id=msg.buffer_id, in_port=pkt_in_port, actions=actions, data=data)
            datapath.send_msg(out_msg) # Packet-Out

        # Case 5b:(Special) Handling Packet-Out when Src-switch and Centre-Switch are the same
        # Flow-mod is handled earlier for this scenario
        else:
            vnf_mac      = sla.VNFsNetworkMac[0]
            vnf_out_port = self.m_mac_to_dpid_port[vnf_mac].val2
            match        = parser.OFPMatch(in_port=pkt_in_port,eth_src=src_mac)
            actions      = [parser.OFPActionSetField(eth_dst=vnf_mac),
                            parser.OFPActionOutput(vnf_out_port)]

            data    = msg.data if msg.buffer_id == ofproto.OFP_NO_BUFFER else None
            out_msg = datapath.ofproto_parser.OFPPacketOut(datapath=datapath, buffer_id=msg.buffer_id, in_port=pkt_in_port, actions=actions, data=data)
            datapath.send_msg(out_msg) # Packet-Out

    # Returns the Path from Centre to the Dest. End-Point
    def getSlaDestPath(self, sla, dst_mac):

        dst_dpid = 0
        for i in range(0,len(sla.endUsersMac)):

            if sla.endUsersMac[i] == dst_mac:
                dst_dpid = sla.endPointsDpid[i]

        return sla.pathToCentre[dst_dpid]


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
                    LOG_DEBUG("This scenario should not occur. Programming Error!!!")
                    break

                current = dctEndPoints[endPoint]['parent'][current]

            pathToCentre[endPoint].append(endPoint)

        return pathToCentre


    def get_sla_flow_path(self, src_dpid, dst_dpid, sla):
        
        # Sanity Check
        if sla.isInstalled == 0:
            LOG_DEBUG("SLA (%s) is not mapped." % sla.identifier + 1)
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

    def DFS_visit(self, src_dpid, dst_dpid, color, path_list):
        u = src_dpid

        for v, port in self.m_graph['edges'][u].items():
            if v in self.m_spTreeLinks and u in self.m_spTreeLinks[v]:
                if color[v] == COLOR_WHITE:
                    color[v] = COLOR_BLACK

                    # Found dst_dpid
                    if v == dst_dpid:
                        path_list = [int(dst_dpid)]
                        return SUCCESS, path_list
                    else:
                        ret_flag, ret_path_list = self.DFS_visit(v, dst_dpid, color, path_list)
                        if ret_flag == SUCCESS:
                            ret_path_list.append(int(v))
                            return ret_flag, ret_path_list

        return FAILURE, None

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
                self.checkIfVNFtoBeInstalled(dpid)
                self.m_graph['switches'].add(switch.dp)

                if dpid not in self.m_graph['edges']:
                    self.m_graph['edges'].setdefault(dpid, {})
                if dpid not in self.m_graph['hosts']:
                    self.m_graph['hosts'].setdefault(dpid,{})

        # Update network's Spanning Tree
        for datapath in self.m_graph['switches']:
            self._calculate_SpanningTree(datapath.id)
            break

    # Check whether any VNFs are to be installed, at startup
    def checkIfVNFtoBeInstalled(self, dpid):
        vnfForSwitch = 's' + str(dpid)
        if vnfForSwitch == 's1':
            
            vnfAtSwitch = self.findApprLocForVNF(vnfForSwitch)

            # Intended users at dpid-1 will be serviced by Firewall at dpid-2
            self.m_vnfs.setdefault(dpid, [])
            self.m_vnfs[dpid].append(make_tuple('firewall', int(vnfAtSwitch.lstrip('s'))))


    # Find appropriate location for the VNF, 
    # Static: Hardcoded
    # Dynamic : TODO To be decided by the Orchestrator's logic
    def findApprLocForVNF(self, switchName):
        if switchName == 's1':
            return 's2'
        else:
            print "Programming Error!!!"


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

        # Update network's Spanning Tree
        for datapath in self.m_graph['switches']:
            self._calculate_SpanningTree(datapath.id)
            break

    # Host Add Event
    @set_ev_cls(event.EventHostAdd, MAIN_DISPATCHER)
    def update_topology_hostAdd(self, ev):

        # Host information
        mac = ev.host.mac
        dpid = ev.host.port.dpid
        port = ev.host.port.port_no

        # Code commented for Testing with Mininet

        if "00:00:00:00:00" not in mac:
            return

        print "Host added @ dpid - %s : %s via port - %s" % (dpid, mac, port)

        #pdb.set_trace()

        # Sanity Check
        if dpid in self.m_graph['hosts'] and mac in self.m_graph['hosts'][dpid] and mac in self.m_mac_to_dpid_port:
            return

        # Maintain the Data-structures
        # m_graph['hosts'] [dpid] [mac] => port
        if mac not in self.m_graph['hosts'][dpid]:
            self.m_graph['hosts'][dpid].setdefault(mac,{})

        self.m_graph['hosts'][dpid][mac]=port

        # mac -> (dpid,port)
        self.m_mac_to_dpid_port[mac] = make_tuple(dpid, port)

        # dpid -> (mac, port)
        if dpid not in self.m_dpid_to_mac_port:
            self.m_dpid_to_mac_port.setdefault(dpid, {})
        self.m_dpid_to_mac_port[dpid][mac] = port

        if False and LOGGING_DEBUG:
            LOG_DEBUG("Saved Host information : " + str(mac) + " : " + str(dpid) + " : " + str(port))

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
                # Improve by using weights among the edges
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


    def _DFS_visit(self, src_dpid, dst_dpid, color, path_list):
        u = src_dpid

        for v, port in self.m_graph['edges'][u].items():
            if v in self.m_spTreeLinks and u in self.m_spTreeLinks[v]:
                if color[v] == COLOR_WHITE:
                    color[v] = COLOR_BLACK

                    # Found dst_dpid
                    if v == dst_dpid:
                        path_list = [dst_dpid]
                        return SUCCESS, path_list
                    else:
                        ret_flag, ret_path_list = self._DFS_visit(v, dst_dpid, color, path_list)
                        if ret_flag == SUCCESS:
                            ret_path_list.append(v)
                            return ret_flag, ret_path_list

        return FAILURE, None

    def get_flow_path(self, dpid1, dpid2):
        ret_path_list = []

        # Sanity Check, same dpid
        if dpid1 == dpid2:
            ret_path_list.append(int(dpid1))
            ret_path_list.append(int(dpid1))
            return ret_path_list

        # Run DFS to get the flow-path
        color = {}
        path_list = []

        for u in self.m_graph['switches']:
            color[u.id] = COLOR_WHITE

        color[dpid1] = COLOR_BLACK

        ret_flag, ret_path_list = self.DFS_visit(dpid1, dpid2, color, path_list)
        ret_path_list.append(int(dpid1))
        return ret_path_list

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
            if end_user not in self.m_endUsersToSLA:
                self.m_endUsersToSLA[end_user] = []

            # The Endpoint may belong to many SLA's
            self.m_endUsersToSLA[end_user].append(sla_object.identifier)

    # Check wether end-users belong to an SLA
    def checkEndUsersToSLA(self, endUser1, endUser2):

        # End-users may belong to many SLAs
        result = []

        if endUser1 in self.m_endUsersToSLA:

            for sla_id in self.m_endUsersToSLA[endUser1]:

                sla_object= self.m_SLAs[sla_id]
                
                # Both endpoints belong to the same SLA
                if endUser2 in sla_object.endUsersMac:
                    result.append(sla_object)

        return result


# -----------------------------------------
# Miscellaneous Functions
# -----------------------------------------

def LOG_DEBUG(string):
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

