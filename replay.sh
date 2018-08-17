#/bin/sh
find . -iname *.proof | xargs -n 1 echo | xargs -n 1 java -Xmx4196m -jar ./key/KeY.jar --auto 
