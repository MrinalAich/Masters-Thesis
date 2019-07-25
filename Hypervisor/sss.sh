# Purposes - 
# 1. Bash shell into a docker container
# 2. Can Force stop all running container bash shells
# 3. Ping from a containter to another container

PROCESS_EXEC_CMD="docker exec"
NO_OF_PACKETS=1000

# Sanity Check
if [ $# -eq 0 ]; then
    echo "Please specify either a container ID or Clear command..."
else
   # Clear all exiting bash shells
   if [ "$1" == "c" ]; then

       kill $(ps aux | grep 'docker exec' | awk '{print $2}')

       clear
       echo "Exiting container shells deleted..."

   else
   # Enter a specific containers bash shell
       clear
       echo -e "Shell script of containter - $1"
       if [ $# -eq 2 ]; then
           echo "ping from $1 to $2"
           remote_cont_name=$2
           id=${remote_cont_name:1:2}
           docker exec -it $1 ping -c $NO_OF_PACKETS 192.168.111.$id
       else
            docker exec -it $1 bash
       fi
  fi
fi
