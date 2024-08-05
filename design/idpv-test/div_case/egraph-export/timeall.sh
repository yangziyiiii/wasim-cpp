solver=~/ziyi/bitwuzla
echo "bitwidth,time" > run.log
for i in {4..65}; do 
  X=`(time $solver smt_$i.smt2) 2>&1 | grep real | cut -f2`
  echo $i,$X
  echo $i,$X >> run.log
done
