Command to execute on each Hypervisor :  

    ===============
    ./xx_server.sh
    ===============



List of files in each Hypervisor and their usages - 
-------------------
command_server.py :
-------------------
    Destroys any existing connection and restarts a Server to receive commands from the Host Machine/Ryu Controller.
    Script receives non-Docker related commands and executes them. e.g. ./run_dckr.sh
    Note : This was created to automate the entire system to start from the end of the Host machince.
    This script needs to be executed on each Hypervisor manually to setup command-interface with the Host machine.

    xx_server.sh : Simpler way to execute the above python script.


-----------------------
automated_scripted.py :
-----------------------
    Read inputs from 'config.txt'.

    Functionalities -
    -> Removes any exisitng configuration such as Script files, Docker Network or Docker Containers.
    -> Creates and executes the Docker Containers as per the configuration mentioned in 'config.txt'.

    Configurable Parameters - 
    Docker Network or Container related parameters which can be configured - 
    1. Name of the Docker Network - default : overnet
    2. Subnet of the Network - default : "192.168.111.0/24"
    3. Max Simultaneous Containers running on a Hypervisor - default : 10
    4. Docker Containers Memory Limit - default : 128 MB

    run_dckr.sh : Simpler way to execute the above python script.

-------------
config.txt :
-------------
    Contains the information about the Hypervisors (Unique Id, IP Address) along with the Docker Containers running on the hydervisors at startup.

    Format - 
    N representing # of Hypervisors.
    Following N lines represents each Hypervisor's unique Id and IP Address.
    M representing # of Hypervisors running any Container.
    Following M lines represents the type of Docker containers running on a Hypervisor.

    e.g.
    3
    1 192.168.122.11
    2 192.168.122.12
    3 192.168.122.13
    2
    1 busy_box busy_box busy_box
    3 iperf3_server busy_box busy_box

    List of supported Docker containers are - 
    busy_box      - centos:latest
    webserver     - nginx_server:1.0
    firewall      - kalilinux/kali-linux-docker 
    ftp           - ftpd_server:1.0
    iperf3_server - networkstatic/iperf3:latest
    iperf3_client - networkstatic/iperf3:latest


-----------------
client_stats.py :
-----------------
    Ryu Controller runs on the Local Host machine and maintains the statistics from the Hypervisors.
    This script runs on each Hypervisor.

    Functionalities -
    -> Collects and sends periodic docker statistics to the Remote Controller for Network Monitoring procedures.
    -> Receives commands to execute from the Remote Controller such as Starting/Closing of a Container, changing configration of a Container.

    Configurable Parameters - 
    1. IP Address and port of the server hosting the Remote Controller.
    2. Docker statistics sending periodic interval.
    

--------
sss.sh :
--------
    Shell script to perform the following functionalities -
    -> To stop and clean all running Containers.
    -> Enter a specific Containers Bash Shell.

    This script is useful for Debugging purposes. e.g. Manually starting a ping/iperf command from a Container to another.
