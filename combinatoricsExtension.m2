--# returns next partition of the same integer in lexicographical order
--# algorithm from "The theory of partitions", George E. Andrews
-- todo: test next Partition!
next= method()
next Partition := Partition => (currPartition) ->(
    tmpList:= new MutableList from currPartition;
    if (#tmpList==0) then return null;
    currSize:= #tmpList;
    currPos := #tmpList-1;
    if (tmpList#currPos>1 ) then 
    (
        tmpList#currPos = tmpList#currPos - 1;
        tmpList= append(tmpList , 1) ;
        return (new Partition from tmpList);
    );
    remainingValue:=0;
    while (tmpList#currPos==1 ) do
        (
            remainingValue=remainingValue+1;
            if (currPos==0) then 
                return null;
            currPos=currPos-1;
        );
    remainingValue =remainingValue + tmpList#currPos;
    nextNum = tmpList#currPos-1;
    while( remainingValue >= nextNum ) do
        (
            if (currPos>=currSize ) then 
            (
                tmpList= append(tmpList , nextNum) ;
            )
            else
                tmpList#currPos  = nextNum;
            remainingValue =remainingValue- nextNum;
           currPos=currPos + 1;
        );
    if (remainingValue > 0) then
        (
            if (currPos>=currSize ) then 
            (
                tmpList=append(tmpList , remainingValue) ;
                currPos=currPos + 1;
            )
            else
            (
                tmpList#currPos  = remainingValue;
                currPos=currPos + 1;
            );
        );
        tmpList=drop(tmpList,{currPos,#tmpList});
        return (new Partition from tmpList);
)

testNextPartition = ()->
(
    num := 40;
    testPar := new Partition from {num} ;
    count:=1;
    while (testPar=!=null) do
    (
        testPar = next testPar;
        count=count+1;
    );
    print count;
)
