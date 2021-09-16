#!/bin/sh


exec java -jar "$0" -Ddyna.runtimejar=$0 -Xmx1g "${@:2}"
exit 0

# what follows is the dyna implementation compiled into a jar
##################################################
