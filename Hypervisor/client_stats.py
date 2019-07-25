import socket, select, string, sys
import random, time, sys, os, json, pdb, subprocess
from thread import *
import threading


# Global variables
HOST = "192.168.225.11"    # Set the server address to variable host
PORT = 4444                # Sets the variable port to 4444
STAT_INTERVAL = 1          # In seconds
HOST_IP = ""               # Assigned later

# System Variables
INTERFACE = "ens3"           # Change as per the System

# Misc variables
BUFFER_SIZE = 4096

# Returns Total usage of Docker Conatainer's CPU utilization
def getDockerStats():

    # Docker command to receive statistics
    cmd = "docker stats --no-stream --format \"{{.CPUPerc}}\""
    p = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    output, err = p.communicate()

    currentTime = time.time()

    cpuUtilization = 0.0
    lines = output.split('\n')
    for index in range(0, len(lines)-1):
        data = lines[index][:-1]
        cpuUtilization += float(data)

    # Format - Hypervisor IP : Current Time : CPU % Utilization
    formattedMsg = "%s:%s:%s" % (HOST_IP, currentTime, cpuUtilization)  

    return str(formattedMsg)

# Retreives IP Address assigned to a particular interface
def getHostIPAddress():

    cmd = "/sbin/ifconfig %s | awk -F ' *|:' '/inet addr/{print $4}'" % INTERFACE
    p = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    output, err = p.communicate()

    return output.rstrip()

# Periodic Thread Fuction
def periodic_thread(s):
    
    while 1:

        # Periodically, collect and send Docker Stats
        msg = getDockerStats()      
        sent = s.send(msg)
        if sent == 0:
            print "Could not sent any Data"    
        time.sleep(STAT_INTERVAL)

# Main function
if __name__ == "__main__":

    HOST_IP = getHostIPAddress()

    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    s.settimeout(2)
     
    # connect to remote host
    try :
        s.connect((HOST, PORT))
        print "Connected to Ryu Server"
    except :
        print 'Unable to connect to Host: %s on Port: %s' % (HOST, PORT)
        sys.exit()

    # Init Periodic Thread
    start_new_thread(periodic_thread, (s,))
   
    # Main thread for Receiving Commands
    while 1:

        socket_list = [s]

        # Get the list of sockets which are readable
        read_sockets, write_sockets, error_sockets = select.select(socket_list, [], [])
         
        for sock in read_sockets:
            # Incoming message from remote Controller
            if sock == s:
                data = sock.recv(BUFFER_SIZE)
                if not data:
                    sys.exit()
                else:
                    # Execute System Command
                    # print " EXECUTING Command: %s" % (data)
                    os.system(data)




