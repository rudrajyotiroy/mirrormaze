git config --global user.name rudrajyotiroy
git config --global user.email rudrajyotiroy@gmail.com
mkdir -p build && cd build
cmake ..
make
echo "Compile done"

if [ $2 = "perf" ]; then
    cd ../benchmarks/performance
    rm -f default.profraw *_prof *_fplicm *.bc *.profdata *_output *.ll
    sh run.sh hw2perf$1
    sh viz.sh hw2perf$1
    echo "Performance $1 done"
elif [ $2 = "correct" ]; then
    cd ../benchmarks/correctness
    rm -f default.profraw *_prof *_fplicm *.bc *.profdata *_output *.ll
    sh run.sh hw2correct$1
    sh viz.sh hw2correct$1
    echo "Correctness $1 done"
else
    echo "Exiting... Specify correctness or performance"
fi