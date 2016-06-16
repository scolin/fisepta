grep -q "\[info\][ ]*glob[ ]*>[ ]*{[ ]*b[ ]*}" $1
[ $? -eq 0 ] || exit 1
grep -q "\[info\][ ]*glob[ ]*>[ ]*{[ ]*c[ ]*}" $1
[ $? -eq 0 ] || exit 1
grep -q "\[info\][ ]*return of variadic[ ]*>[ ]*a" $1
[ $? -eq 0 ] || exit 1
