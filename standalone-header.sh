#!/bin/bash

self="$0"
version="VERSION_STRING"

welcome_message() {
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
echo "     \     Impelemented by                  / /          \                   "
echo "      \       Matthew Francis-Landau       / /            \                  "
echo "       \                  (2020-2023)     / /              \                 "
echo "        \                                / /                \                "
echo "         \                              / /                  \               "
echo "          \                            / /                    \              "
echo "           \                          / /                      \             "
echo "            \                        / /                        \            "
echo "             \                      / /                          \           "
echo "              \                    / /                            \          "
echo "               \                  / /                              \         "
echo "                \                / /                                \        "
echo "                 \              / /         http://dyna.org          \       "
echo "                  \            / /                                    \      "
echo "                   \          / /                                      \     "
echo "                    \        / /    https://github.com/argolab/dyna3    \    "
echo "                     \      / /                                          \   "
echo "                      \    / /                                            \  "
echo "                       \  / /                                              \ "
echo "                        \/ --------------------------------------------------"
echo "                                                                             "
}

help() {
    echo "Dyna implemented using R-exprs"
    echo ""
    echo "     --help                Print this message"
    echo "     --memory=1G           Set the amount of memory for the JVM"
    echo "     --import [file name]  Import some a file into the REPL from the command line"
    echo "     --csv-import [term name] [file name]"
    echo "     --csv-export [term name] [file name]"
    echo "     --time                Time the different parts of the runtime report when the program exits"
    echo "     --fast-math           Do not check the math operations for numerical overflow"
    echo "     --print-agenda        Print out the work that the agenda is doing"
    echo "     --random-seed=42      Set a random seed"
    echo "     --version             Print out version"
    echo ""
    echo "Usage: $self [args] [file to start]"
    echo ""
    echo "To install the Python package for Dyna run: $self install-python"
}

install_python() {
    t=`mktemp -d`
    trap "rm -rf $t" EXIT
    set -x

    unzip -qq "$self" "dyna_python_module/*" -d $t 2>/dev/null
    cp "$self" $t/dyna_python_module/dyna/dyna.jar
    cd $t/dyna_python_module
    python setup.py install
}

# set dyna to use a different java runtime
if [ -z "${DYNA_JVM}" ]; then
   DYNA_JVM='java'
fi

which $DYNA_JVM 2>/dev/null >/dev/null
if [ $? -ne 0 ]; then
    echo "Unable to find Java in the path ($PATH)."
    echo ""
    echo "Either install Java or provide a path to the Java runtime using: "
    echo "    export DYNA_JVM=/path/to/java-install/bin/java"
    exit 1
fi


dyna_args=""
import_args=""
jvm_args="-Xss16m "
memory="${DYNA_MEMORY:-4G}"
perf_mode="safe"
debug_mode="false"

while [ $# -gt 0 ]; do
    case "$1" in
        --memory*)
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
        --version)
            echo "Version: $version"
            exit 1
            ;;
        -agentlib*|-D*|-XX*)
            jvm_args+="$1 "
            ;;
        --time)
            jvm_args+="-Ddyna.time_running=true "
            ;;
        --debug-dyna-impl)
            # this turns on additional debugging stuff in the implementation
            # this should not need to be used
            debug_mode="true"
            ;;

        --print-agenda)
            jvm_arg+="-Ddyna.print_agenda_work=true -Ddyna.print_agenda_progress=true -Ddyna.print_agenda_running=true "
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
        # --fast)
        #     # maybe should just set this at the same time as debug
        #     jvm_arg+="-Ddyna.check_rexprs_args=false "
        #     ;;


        --import|--run)
            [[ -f "$2" ]] || {
                echo "File $2 not found"
                exit 2
            }
            import_args+="$1 $2 "  # this could go into a different array for just the import statements?
            shift
            ;;
        --csv-import|--csv-export)
            [[ "$2" =~ ^[a-z][a-zA-Z0-9_]*\/[0-9]+$ ]] || {
                echo "term '$2' did not match expected 'name/arity'"
                exit 2
            }
            import_args+="$1 \"$2\" \"$3\" "
            shift
            shift
            exit 1  # TODO implement this
            ;;

        --random-seed*)
            seed="${1#*=}"
            [[ $seed =~ ^[0-9]+$ ]] || {
                echo "--random-seed expected a number, expected something like: --random-seed=42"
                exit 1
            }
            jvm_args+="-Ddyna.random_seed=$seed "
            ;;

        install-python)
            welcome_message
            echo
            echo '~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~'
            echo 'Python environment:'
            python -m site
            echo ''
            python -c 'import sys; print("Python prefix:", sys.prefix)'
            echo '~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~'
            echo ''
            echo "Install Dyna into the current Python environment?"
            read -p "Are you sure? (y/N) " -n 1 -r
            echo
            if [[ $REPLY =~ ^[yY]$ ]]; then
                install_python
                exit 0
            else
                echo "Install canceled"
                exit 1
            fi
            ;;

        install-python-no-confirm)
            install_python
            exit 0
            ;;

        *)
            # I suppose that the program which is running on dyna could also
            # take command line arguments, so maybe we can not check if the
            # arguments passed are valid, in which case this is going to have to
            # start the whole runtime before it returns an error

            # [[ -f "$1" ]] || {
            #     echo "file not found: $1"
            #     echo "Use `$self --help` to see command line arguments"
            #     exit 2
            # }
            dyna_args+="$1 "
            ;;
    esac
    shift
done


if [ -z "$dyna_args" ]; then
    welcome_message
    printf "Loading...\r"
    jvm_args+=" -Ddyna.loading_spin=true "
fi

jvm_args="-Xmx$memory -Dclojure.compiler.direct-linking=true -Ddyna.print_rewrites_performed=false -Ddyna.debug=$debug_mode -Ddyna.trace_rexpr_construction=$debug_mode -Ddyna.debug_repl=$debug_mode -Ddyna.check_rexprs_args=$debug_mode $jvm_args"
# -XX:-StackTraceInThrowable  # disable stack traces entirely

exec $DYNA_JVM $jvm_args "-Ddyna.runtimejar=$self" -jar "$self" $import_args $dyna_args
exit 1  # should not get to this line

# what follows is the dyna implementation compiled into a jar
#############################################################
