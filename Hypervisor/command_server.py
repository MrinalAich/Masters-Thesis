import socket, select, string, sys
import random, time, sys, os, json, pdb, subprocess
from thread import *
import threading, pdb

# Global variables
IP_ADDR         = "0.0.0.0"
PORT            = 5555       # Sets the variable port to 5555
STAT_INTERVAL   = 1          # In seconds

# Misc variables
BUFFER_SIZE = 4096


# Main function
if __name__ == "__main__":

    # Stop any process running on this Port
    os.system("kill $(lsof -t -i:%s)" % PORT)

    # Socket-level functions
    server_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    server_socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    server_socket.bind((IP_ADDR, PORT))
    server_socket.listen(1)


    # Add server socket object to the list of readable connections
    hypervisor_socket_list = []
    hypervisor_socket_list.append(server_socket)

    while 1:
        # get the list sockets which are ready to be read through select
        # 4th arg, time_out  = 0 : poll and never block
        ready_to_read,ready_to_write,in_error = select.select(hypervisor_socket_list,[],[],0)
      
        for sock in ready_to_read:
            # new connection request recieved
            if sock == server_socket: 
                sockfd,addr= server_socket.accept()
                os.system("clear")
                print "Command Hypervisor Connection established"
                hypervisor_socket_list.append(sockfd)

            # message from a Hypervisor system, not a new connection
            else:
                data = sock.recv(BUFFER_SIZE)
                if data:
                    # Execute Command on the Hypervisor
                    print "Received Command: |%s|" % data
                    try:
                        os.system(data)
                    except:
                        continue
                else:
                    # Remove the socket that's broken
                    if sock in hypervisor_socket_list:
                        hypervisor_socket_list.remove(sock)
                        sock.close()

    server_socket.close()

