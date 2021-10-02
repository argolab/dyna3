#!/bin/bash

self="$0"

help() {
    echo "Dyna implemented using R-exprs"
    echo ""
    echo "     --help                Print this message"
    echo "     --memory=1G           Set the amount of memory for the JVM"
    echo "     --import [file name]  Import some a file into the REPL from the command line"
    echo "     --csv-import [term name] [file name]"
    echo "     --csv-export [term name] [file name]"
    echo "     --time                Time the different parts of the runtime report when the program exits"
    echo "     --fast-math           Do not check the math for overflow"
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
echo "          _____   __     __  _   _                ____         ___           "
echo "         |  __ \  \ \   / / | \ | |     /\       |___ \       / _ \          "
echo "         | |  | |  \ \_/ /  |  \| |    /  \        __) |     | | | |         "
echo "         | |  | |   \   /   | . \` |   / /\ \      |__ <      | | | |         "
echo "         | |__| |    | |    | |\  |  / ____ \     ___) |  _  | |_| |         "
echo "         |_____/     |_|    |_| \_| /_/    \_\   |____/  (_)  \___/          "
echo "                                                                             "
# echo "                _____   __     __  _   _                                     "
# echo "               |  __ \  \ \   / / | \ | |     /\                             "
# echo "               | |  | |  \ \_/ /  |  \| |    /  \                            "
# echo "               | |  | |   \   /   | . \` |   / /\ \                           "
# echo "               | |__| |    | |    | |\  |  / ____ \                          "
# echo "               |_____/     |_|    |_| \_| /_/    \_\                         "
# echo "                                                                             "
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
import_args=""
jvm_args=""
memory="2G"
perf_mode="safe"

while [ $# -gt 0 ]; do
    case "$1" in
        --memory=*)
            memory="${1#*=}"
            [[ $memory =~ ^[0-9]+[gGmMkK]$ ]] || {
                echo "--memory argument was unexpected, expected number and suffix E.g. --memory=10g"
                exit 2
            }
            ;;
        --help)
            help
            exit 1
            ;;
        -agentlib*|-D*|-XX*)
            jvm_args+="$1 "
            ;;
        --time)
            jvm_args+="-Ddyna.time_running=true "
            ;;

        # --fast)
        #     perf_mode="fast"
        #     ;;
        # --fast-math)
        #     perf_mode="fast-math"
        #     ;;
        # --

        --fast-math)
            # this will turn off overflow checking on the math operators, which will make the runtime faster
            jvm_args+="-Ddyna.unchecked_math=true "
            ;;
        --fast)
            jvm_arg+="-Ddyna.check_rexprs_args=false "
            ;;


        --import)
            [[ -f "$2" ]] || {
                echo "File $2 not found"
                exit 2
            }
            import_args+="$1 $2 "  # this could go into a different array for just the import statements?
            shift
            ;;
        --csv-import|--csv-export)
            [[ "$2" =~ ^[a-z][a-zA-Z0-9]*\/[0-9]+$ ]] || {
                echo "term '$2' did not match expected 'name/arity'"
                exit 2
            }
            import_args+="$1 \"$2\" \"$3\" "
            shift
            shift
            exit 1  # TODO implement this
            ;;

        install-python)
            exit 1  # TODO, will need the python package included into the jar
            echo "Install the dyna runtime package to the current python environment"
            install_python
            exit 0
            ;;

        *)
            dyna_args+="\"$1\" "
            ;;
    esac
    shift
done

jvm_args+="-Xmx$memory "

if [ -z "$dyna_args" ]; then
   copy_right
fi


exec java $jvm_args -Ddyna.runtimejar=$self -jar "$self" $import_args $dyna_args
exit 0

# what follows is the dyna implementation compiled into a jar
##################################################
