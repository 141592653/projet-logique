echo "     ##### [Test1 OPTIONAL] computing md5 (16 steps) ... #####"
./hackMD -v -c exemples/0-input.hex
echo "\nThe implementation of reference returns..."
./md5 exemples/0-input.hex

echo "\n\n     ##### [Test2 OPTIONAL] computing md5 (64 steps) ... #####"
./hackMD -v -r 4 -s 16 -c exemples/0-input.hex
echo "\nThe implementation of reference returns..."
./md5 exemples/0-input.hex -full

echo "\n\n     ##### [Test3] inverting md5... #####"
./hackMD -v -r 1 -s 16 exemples/0-digest.hex

echo "\n\n     ##### [Test4] inverting md5 with partial info about input... #####"
./hackMD -v -r 1 -s 16 -p 224 exemples/malicious-partial-input.hex exemples/honest-digest.hex
echo "\n  # The text:"
echo -n "<<"
cat exemples/honest-input.hex | xxd -r -p
echo -n "\n>>"
echo "\n  # has the same MD5-digest (16 steps) as the following malicious text:"
echo -n "<<"
cat exemples/honest-digest__inputFound.out | xxd -r -p
echo -n "\n>>"
echo "\n # Verification:"
./md5  exemples/honest-digest__inputFound.out
./md5  exemples/honest-input.hex
