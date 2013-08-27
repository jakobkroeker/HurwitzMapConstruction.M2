#!/bin/bash
export MACAULAY2_SHARE_PATH=~/.Macaulay2/local/share/Macaulay2
export RFSDIR=rationalFunctionSearch
mkdir -p $MACAULAY2_SHARE_PATH
mkdir -p $MACAULAY2_SHARE_PATH/$RFSDIR
cp ./padicLift.m2  $MACAULAY2_SHARE_PATH
cp ./rationalFunctionSearch.m2 $MACAULAY2_SHARE_PATH/
cp ./rationalFunctionSearch/rfsObjects.m2 $MACAULAY2_SHARE_PATH/$RFSDIR/
cp ./rationalFunctionSearch/rfsIO.m2 $MACAULAY2_SHARE_PATH/$RFSDIR/
cp ./rationalFunctionSearch/rfsPrepareLift.m2 $MACAULAY2_SHARE_PATH/$RFSDIR/
cp ./rationalFunctionSearch/rfsTests.m2 $MACAULAY2_SHARE_PATH/$RFSDIR/


