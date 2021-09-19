#!/bin/bash

self="$0"

help() {
    echo "Dyna implemented using R-exprs"
    echo ""
    echo "     --help       Print this message"
    echo "     --memory=1G  Set the amount of memory for the JVM"
    echo ""
    echo "Useage: $self [args] [file to start]"
    echo ""
    echo "To install python package for dyna: $self install-python"
}

install_python() {
    t=`mktemp -d`
    trap "rm -rf $t" EXIT

    unzip $self "dyna_backend/install-python-package" -d $t
    cp $self $t/some-path-in-the-install-dir/dyna
    pushd $t
    pip install .
    popd
}

copy_right() {
echo "                _____   __     __  _   _                                     "
echo "               |  __ \  \ \   / / | \ | |     /\                             "
echo "               | |  | |  \ \_/ /  |  \| |    /  \                            "
echo "               | |  | |   \   /   | . \` |   / /\ \                           "
echo "               | |__| |    | |    | |\  |  / ____ \                          "
echo "               |_____/     |_|    |_| \_| /_/    \_\                         "
echo "                                                                             "
echo "-------------------------------------------------- /\                        "
echo " \                                              / /  \                       "
echo "  \                                            / /    \                      "
echo "   \                                          / /      \                     "
echo "    \                                        / /        \                    "
echo "     \                                      / /          \                   "
echo "      \                                    / /            \                  "
echo "       \                                  / /              \                 "
echo "        \                                / /                \                "
echo "         \                              / /                  \               "
echo "          \                            / /                    \              "
echo "           \                          / /                      \             "
echo "            \                        / /                        \            "
echo "             \                      / /                          \           "
echo "              \                    / /                            \          "
echo "               \                  / /                              \         "
echo "                \                / /                                \        "
echo "                 \              / /                                  \       "
echo "                  \            / /                                    \      "
echo "                   \          / /                                      \     "
echo "                    \        / /                                        \    "
echo "                     \      / /                                          \   "
echo "                      \    / /                                            \  "
echo "                       \  / /                                              \ "
echo "                        \/ --------------------------------------------------"
echo "                                                                             "
echo "                                 Impelemented By                             "
echo "                                      Matthew Francis-Landau (2020-2021)     "
# echo ""
# echo "                                      https://github.com/matthewfl/dyna-R/   "
echo ""
}

dyna_args=""
jvm_args=""
memory="2G"

while [ $# -gt 0 ]; do
    case "$1" in
        --memory=*)
            memory="${1#*=}"
            ;;
        --help)
            help
            exit 1
            ;;
        -agentlib*|-D*|-XX*)
            jvm_args+="$1 "
            ;;

        install-python)
            echo "Install the dyna runtime package to the current python environment"
            install_python
            exit 0
            ;;

        *)
            dyna_args+="$1 "
            ;;
    esac
    shift
done

jvm_args+="-Xmx$memory "

if [ -z "$dyna_args" ]; then
   copy_right
fi


exec java $jvm_args -Ddyna.runtimejar=$self -jar "$self"  $dyna_args
exit 0

# what follows is the dyna implementation compiled into a jar
##################################################
