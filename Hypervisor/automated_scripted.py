import subprocess, os, sys
from collections import defaultdict

# Data Structures
node_ip_pair = {}
node_cont_list = defaultdict(list)

# Initializations
 ## Node Specific
node_id = ""
ovs = ""
dpid = ""

 ## Docker specific
net_name="overnet"
subnet_ip="192.168.111.0/24"


controller_port  = 6633
    
# Script Specific Parameters
configuration_file = "config.txt"
MAX_CONTAINER_PER_NODE = 10

''' ### Function prototypes -- 

# Network related

    setup_network()
    execute_container(container_type, container_id)

# Configuration related
    remove_existing_config()
    print_config_file()
    read_config_file()   

# Miscellaneous
    print_running_containers(containers)
    
'''

def main():
    global node_id, ovs, dpid

    node_id = 1

    # Remove previous Configuration, if any
    remove_existing_config()

    # Only Clean option
    if len(sys.argv) >= 2:
        clear_flag = str(sys.argv[1]) if len(sys.argv) == 2 else str(sys.argv[2])
        if clear_flag == "clean" or clear_flag == "clear" or clear_flag == "c":
            os.system("pkill -f 'python client_stats.py'")
            #os.system("pkill -f 'python command_server.py'")
            os.system("clear");
            return

    # Read configuration file
    read_config_file()

    # Print Configuration file
    print_config_file()
    
    # Create new Configuration
    setup_network()

    # CPU utilization Client App
    if os.path.exists("client_stats.py"):
        os.system("python client_stats.py &");
    else:
        print "Cannot start Client App. File does not exists!!!"

       
# ------------------------------------------------------------------
## Utility Functions
# ------------------------------------------------------------------
# Setup the Network
def setup_network():

    # Create Docker Network
    os.system("docker network create -d bridge --subnet=%s %s" % (subnet_ip,net_name))

    #os.system("ip link add intap0 type veth peer name intap1")
    os.system("ls /sys/class/net | grep br | xargs -I%  brctl addif \"%\" ens8")
    #os.system("ovs-vsctl add-port %s intap1" % ovs)
    #os.system("ip link set intap0 up")
    #os.system("ip link set intap1 up")

    # Run Containers
    containers = []
    container_id = 0

    for container_type in node_cont_list[node_id]:
        container_id = container_id + 1
        container_details = execute_container(container_type, container_id)
        if container_details is not None:
            containers.append(container_details)
        # Sanity Check
        if container_id == MAX_CONTAINER_PER_NODE:
            print "Maximum possible containers are running for node-%s" % node_id
            break

    os.system("clear");

    # Print all running containers
    print_running_containers(containers)

# Executing a particular Container
def execute_container(container_type, container_id):
    message = None

    # BusyBox
    if container_type == "busy_box":
        cont_name = "c%s%s" % (node_id,container_id)
        cont_ip = "192.168.111.%s%s" % (node_id,container_id)
        os.system("docker run -d --mac-address=\"00:00:00:00:00:%s%s\" --name %s --network=%s --ip=%s centos:latest sleep 10000" % (node_id, container_id, cont_name, net_name, cont_ip))

    # Web Server
    elif container_type == "webserver":
        cont_name = "w%s%s" % (node_id,container_id)
        cont_ip = "192.168.111.%s%s" % (node_id,container_id)    
        os.system("docker run -d --mac-address=\"00:00:00:00:00:%s%s\" --name %s --network=%s --ip=%s nginx_server:1.0" % (node_id, container_id, cont_name, net_name, cont_ip))

    # FTP Server
    elif container_type == "ftp":
        cont_name = "ftp%s%s" % (node_id,container_id)
        cont_ip = "192.168.111.%s%s" % (node_id,container_id)
        os.system("docker run -d --name %s --mac-address=\"00:00:00:00:00:%s%s\" --network=%s --ip=%s -p 21:21 -e \"PUBLICHOST=localhost\" ftpd_server:1.0" % (node_id, container_id, cont_name, net_name, cont_ip))
        message = "FTP Server: Please enter login credentials in FTP server."
    
    # Firewall
    elif container_type == "firewall":
        cont_name = "f%s%s" % (node_id,container_id)
        cont_ip = "192.168.111.%s%s" % (node_id,container_id)
        os.system("docker run -d --mac-address=\"00:00:00:00:00:%s%s\" --name %s --network=%s --ip=%s --privileged kalilinux/kali-linux-docker sleep 10000" % (node_id, container_id, cont_name, net_name, cont_ip))

        os.system("docker exec -it %s echo 1 \> /proc/sys/net/ipv4/ip_forward" % cont_name)
        os.system("docker exec -it %s iptables -F" % cont_name)
        os.system("docker exec -it %s iptables -A OUTPUT -j DROP" % cont_name)
        os.system("docker exec -it %s iptables -A FORWARD -i eth0 -o eth0 -j ACCEPT" % cont_name)

    # Iperf-client
    elif container_type == "iperf3_client":
        cont_name = "c%s%s" % (node_id,container_id)
        cont_ip   = "192.168.111.%s%s" % (node_id,container_id)
        os.system("docker run -d --mac-address=\"00:00:00:00:00:%s%s\" --name %s --network=%s --ip=%s networkstatic/iperf3:latest -c 192.168.111.22:9922" % (node_id, container_id, cont_name, net_name, cont_ip))

    # Iperf-server
    elif container_type == "iperf3_server":
        cont_name = "c%s%s" % (node_id,container_id)
        cont_ip   = "192.168.111.%s%s" % (node_id,container_id)
        cont_port = int("99%s%s" % (node_id, container_id))
        os.system("docker run -d --mac-address=\"00:00:00:00:00:%s%s\" --name %s -p %s:%s --network=%s --ip=%s networkstatic/iperf3:latest -s" % (node_id, container_id, cont_name, cont_port, cont_port, net_name, cont_ip))
        message = "Iperf Server (%s) started at public port: %s." % (cont_name, cont_port)

    else:
        print "Container %s not supported." % container_type
        return None

    return [container_type,cont_name,cont_ip,message]

def remove_existing_config():
    os.system("pkill -f 'pyhton client.py'") # Delete previous running client.py
    os.system("docker rm -f $(docker ps -a -q)") # Remove all docker containers
    os.system("docker network rm %s" % net_name) # Delete the docker custom network

# Print Node Specific Configuration
def print_config_file():

    print "Node-%s status..." % node_id

    # Print Nodes - IP
    for val,key in node_ip_pair.items():
        if val == node_id:
            print "IP: " + str(key)

    # Print Nodes - Containers
    for u,key in node_cont_list.items():
        if u == node_id:
            string = "Containers - "
            for v in key:
                string = string + " " + str(v)
            print string

# Reads from a configuration file
def read_config_file():
    global node_ip_pair,node_cont_list 

    node_ip_pair = {}
    node_cont_list = defaultdict(list)

    file = open(configuration_file, "r")

    # Retreive # No.of nodes
    nodes = int(file.readline().rstrip())
    for i in range(nodes):
        line = file.readline().strip()
        words = line.split()
        node_ip_pair[int(words[0])] = words[1].strip("\n ")

    # Retreive Containers
    containers_num = int(file.readline().rstrip())
    for i in range(containers_num):
        line = file.readline().strip()
        words = line.split()

        node = int(words[0])

        if node not in node_cont_list:
            node_cont_list[node] = []

        for i in range(1, len(words)):
            node_cont_list[node].append(words[i].strip("\n "))
    print node_cont_list
     
# Prints all running containers
def print_running_containers(containers):

    for details in containers:
        print "%s: %s - %s" % (details[0],details[1],details[2])
        if( details[3] is not None ):
            print details[3]

    return

# Main function
if __name__ == "__main__": main()

