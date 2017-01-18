#!/bin/sh
die () {
  echo "*** mkall.sh: $*" 1>&2
  exit 1
}
msg () {
  echo "$*"
}
apps="`ls app/*/makefile|sed -e 's,app/,,' -e 's,/makefile,,'`"
sats="`ls sat/*/makefile|sed -e 's,sat/,,' -e 's,/makefile,,'`"

## Uncomment and update to only build selected solver-app pairs
#apps="genipasat genipamax"
#sats="cominisatps2sun cominisatps2sun_nopre cryptominisat4auto cryptominisat4"
#sats="riss_521 riss_600"
#sats="abcdsat_inc"
#sats="glucose4"


#Ours :)
apps="ipasir-incremental"
sats="cominisatps2sun"


[ x"$sats" = x ] && die "no 'sat/*/makefile' found"
for app in $apps
do
  for sat in $sats
  do
    msg "scripts/mkone.sh $app $sat"
    scripts/mkone.sh $app $sat
  done
done
