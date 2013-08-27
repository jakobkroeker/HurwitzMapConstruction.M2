
getDefaultNormalizationOrder = ()->
(
    return {infinity,0,1};
)

deepCopy = method();


------------------------


RFSPolynomialRing = new Type of PolynomialRing


-- not used;  causes problems in usage: ring ( RFSPolynomialRing element)  is not RFSPolynomialRing but rng!
new RFSPolynomialRing from PolynomialRing := (A,rng)->
(
    assert(#(gens  rng)==1 or #(gens  rng)==2);
   --assert(rng#?"commonVariable");
   --assert(rng#?"homogenVariable");
  
   rng#"commonVariable" = first gens  rng;
  if (#(gens rng)==2) then 
    rng#"homogenVariable"=(last gens rng)
   else rng#"homogenVariable"=null;
  return rng;
);

createRFSRing = method();
createRFSRing(ZZ):=(charac)->
(
    assert(isPrime(charac));
    s := null;
    t := null;
    rng := ZZ/charac[symbol t,symbol s];
    
    rng.commonVariable  = (gens rng)#0;
    rng.homogenVariable = (gens rng)#1;

    rng#"commonVariable" = (gens rng)#0;
    rng#"homogenVariable" = (gens rng)#1;
    return rng;
)

commonVariable=method();
commonVariable( PolynomialRing ) := (rng)-> 
(
   if (rng#?"commonVariable") then
        return rng#"commonVariable"
   else return null; 
)

homogenVariable=method();
homogenVariable ( PolynomialRing ) := (rng)-> 
(
 if (rng#?"homogenVariable") then
        return rng#"homogenVariable"
    else return null; 
)

getVariableIdx = method();
getVariableIdx (PolynomialRing,RingElement) := (rng,variable)->
(
    for pos in 0..#(gens rng)-1 do
        if (variable==(gens rng)#pos) then 
            return pos;
    return null;
)

-------------------------------------------------------------------------------------

Shape = new Type of HashTable


-- todo: should an empty shape be possible?
new Shape:= (xyz)->
(
  new HashTable from {("shape",{}), ( "dual",{} ) }
)


new Shape from Thing := (A,c)->
(
  print ("cannot create "|toString A|" from "| toString c); assert (false); 
);

isAShape = (mulstruct) ->
(
    try
    (
      lastEntry := null;
        for pos from 0 to #(mulstruct)-1 do
        (
            
            if ( (ring mulstruct#pos) =!= ZZ ) then
                return false;
            if (pos>0) then 
              if (lastEntry<mulstruct#pos) then 
              (
                print "factor exponents must be sorted from highest to lowest value!";
                return false;
              );
            if ( mulstruct#pos < 1 ) then
                return false;
            lastEntry = mulstruct#pos;
        );
    )
    then
    return true
    else return false;
)

new Shape from BasicList := (A,c)->
(
  if ( isAShape(c) ) then 
    return new HashTable from {("shape",new Partition from c), ("dual",  conjugate new Partition from c), ("degree", sum new List from c) }
  else 
  (
    print ("cannot create "|toString A|" from "| toString c);
    assert (false); 
  );
);

deepCopy (Shape) := (shape)->
(
    return new Shape from shape#"shape";
)


-- note : append (Partition) does not result in a correct Partition. How to fix? - Specialization of append() seems to be ignored.  Jakob wontfix.



new Shape from Partition := (A,c)->
(
  preshape := new Partition from c;
  if ( isAShape(preshape) ) then 
     return new HashTable from {("shape",preshape ), ("dual", conjugate new Partition from c), ("degree", sum new List from c) }
  else 
  (
    print ("cannot create "|toString A|" from "| toString c);
    assert (false); 
  );
);

 
new Shape of Thing from Thing := (A, B, c)->
( 
  print ("cannot create "|toString A|" of "|toString B|" from given "| toString c); assert(false); 
);

new Shape from Shape := (A,c)->( return c; );


size (Shape):=(shape)->(#shape#"shape")

degree (Shape):=(shape)->( shape#"degree" )

exponents (Shape):=(shape)->( new List from shape#"shape" )

partition (Shape):=(shape)->( shape#"shape" )

removeExponent = method();
removeExponent (Shape, ZZ ):= Shape => (parShape, parExponent)->(
  exponentPos := position(exponents parShape, (exp)->exp==parExponent);
  if (exponentPos=!= null) then 
    return new Shape from drop (exponents parShape, {exponentPos,exponentPos})
  else
  (
    --print "shape does not contain given exponent";
    return parShape;
  );
)
---------------------

RFSShapeList = new  Type of List;

new RFSShapeList := (A)->
(
    return {};
)

new RFSShapeList from List := (A,shapeList)->
(
    apply(shapeList,el->(assert(class el=== Shape);));
    if (#shapeList>0) then
    (
        shapeDegree:= degree shapeList#0;
        apply(shapeList,el->(assert(degree el==shapeDegree);));
    );
    return shapeList;
)


deepCopy (RFSShapeList) := (shapeList)->
(
    return new RFSShapeList from (apply(shapeList,shape->deepCopy shape) );
)

findMinPenaltyPos = method(Options=>{"missingDegreeOneFactorPenalty"=>false});
findMinPenaltyPos (RFSShapeList) :=  opts ->( shapeList )->
(
    optimalPos := null;
    minPenalty := null;
    for pos in 0..#shapeList-1 do
    (
           shape:=shapeList#pos;
           uexp := unique exponents shape;
           counts:= apply(uexp,exp->#(select(exponents shape, (val)->(val==exp))));
           penalty := max counts;
            if (opts#"missingDegreeOneFactorPenalty" and (min counts)>1) then 
                penalty = infinity;
            if ( optimalPos===null or minPenalty>penalty) then
           (
                optimalPos = pos;
                minPenalty = penalty;
            )
    );
    return optimalPos;
)

reorderShapeList = method(Options=>{"missingDegreeOneFactorPenalty"=>false})
reorderShapeList (RFSShapeList) := RFSShapeList=> opts -> (shapeList)->
(
    assert (#shapeList>=2);
    resultShapeList:={};
    shapeListCopy := copy shapeList;
    minPenaltyPos:=null;
    for pos in 0..(min (3,#shapeList) -1) do
    (
        minPenaltyPos = findMinPenaltyPos(shapeListCopy,"missingDegreeOneFactorPenalty"=>opts#"missingDegreeOneFactorPenalty");
        resultShapeList= append( resultShapeList,shapeListCopy#minPenaltyPos );
        shapeListCopy = drop(shapeListCopy,{minPenaltyPos,minPenaltyPos});
    );
   -- switch first and second shapes in the list, because it is needed to be able to apply the infinity normalization to the second factor
   resultShapeList= switch (0,1,resultShapeList);
   return ( resultShapeList | shapeListCopy);
)

degree (RFSShapeList) :=(shapeList)->
( 
    if (#shapeList>0) then 
        return (degree shapeList#0)
    else return null;
)

minCharacteristic = method();
minCharacteristic (RFSShapeList) :=(shapeList)->
(
    localMaxExponent:=null;
    for shape in shapeList do
    for currExponent in exponents shape do
    if ((localMaxExponent===null) or localMaxExponent<currExponent) then 
            localMaxExponent=currExponent;
    minCharacteristic := localMaxExponent+1;
    while (not isPrime minCharacteristic) do
            minCharacteristic=minCharacteristic+1;
    return minCharacteristic;
)


--------------------------------------------------------

-- TODO: usage of ShapeLog is not safe - 
ShapeLog = new Type of MutableHashTable;


new ShapeLog:= (xyz)->
(
    return new MutableHashTable;  
)


new ShapeLog from Thing := (A,c)->
(
  print ("cannot create "|toString A|" from "| toString c); assert (false); 
);

new ShapeLog of Thing from Thing := (A, B, c)->
( 
  print ("cannot create "|toString A|" of "|toString B|" from given "| toString c); assert(false); 
);

new ShapeLog from ShapeLog := (A,c)->( return c; );


shapeLogAddConstructionRules = method()

shapeLogAddConstructionRules(ShapeLog, Thing):= ShapeLog=> (shapeLogger, constructionRules) ->
(
   currPos := #shapeLogger;
   shapeLogger#currPos = new MutableHashTable;
   shapeLogger#currPos#"constructionRules" = constructionRules;
   shapeLogger#currPos#"log" = tally{};
   shapeLogger
)



-- TODO : addShapeLog should be typesafe in regard to 
addShapeLog = method()
addShapeLog (ShapeLog,Shape) :=  (shapeLogger, shape) ->
(
  if (#shapeLogger==1) then 
  (
    shapeLogger#0#"log"=shapeLogger#0#"log" + tally { exponents shape };
    shapeLogger
  )
  else assert(false);
)

addShapeLog (ShapeLog,ZZ,Shape) :=  (shapeLogger, addPos, shape) ->
(
  if (shapeLogger#?addPos) then 
  (
    shapeLogger#addPos#"log"=shapeLogger#addPos#"log" + tally { exponents shape };
    shapeLogger
  )
  else assert(false);
)

findLogByRuleStructure = method()
findLogByRuleStructure (ShapeLog, HashTable) :=(shapelog, rulestructure) ->
(
  for currKey in keys shapelog do 
  (
    currLog := shapelog#currKey;
    structureIsEqual := true;
    for whichPolynomial in keys rulestructure do
    (
      assert( currLog#?"ruleStructure");
      --print ("whichPolynomial: " | whichPolynomial);
      assert(currLog#"ruleStructure"#?whichPolynomial);
      if (currLog#"ruleStructure"#?whichPolynomial and
          currLog#"ruleStructure"#whichPolynomial != rulestructure#whichPolynomial) then 
        structureIsEqual = false;
    );
    if (structureIsEqual) then return currLog;
  );
  return null;
)


------------------------------------------------------------------------

isIrreducible = method()
isIrreducible (RingElement) := Boolean=> (univarPoly)->
(
  return (#(factor univarPoly) == 1 and (factor univarPoly)#0#1==1 );
)

-- too slow if not in kernel
-- see givaro for fast irreducibility test?
isIrreducibleByRabinTest = (univarPoly, variable)->
(
  characteristic := char ring univarPoly;
  polDegreeList := (degree univarPoly);
  if (#polDegreeList==0) then 
    return true;
    polDegree:= polDegreeList#0;
  degreeFactor := factor polDegree;
  exponentList := apply(#degreeFactor, pos->characteristic^(polDegree/(degreeFactor#pos#0)));
  --print exponentList;
    modPol:=null;
  for currExponent in exponentList do
  (
    modPol = (variable^currExponent - variable );
    --modPol = modPol-(modPol//univarPoly)*univarPoly;
    if (gcd (univarPoly,modPol) != 1) then
      return false;
  );
  modPol = variable^(characteristic^polDegree)-variable;
  --print modPol;
  rest := modPol-(modPol//univarPoly)*univarPoly;
  --print rest;
  if (rest != 0 ) then
    return false;
  return true;  
)

-- works only for polynomial degree 1..3
pseudoIsIrreducibleCondFkt = (polynomial)->
(
    --#0==#(allRationalZeros(polynomial,(commonVariable ring polynomial)  ))
    not hasRationalZeros(polynomial,(commonVariable ring polynomial)  )
)

trueCondition = (polynomial)->
(
   true
)

createPseudoIsIrreducibleCondFkt = (rng)->
(
    characteristic := char rng;
    variable:= commonVariable rng;
    fkt:= (polynomial)->
    (
    for fieldElem from 0 to characteristic-1 do
    (
        
        if (sub(polynomial,variable=>fieldElem_rng)==0) then
            return false;
    );
    return true;
    );
    return fkt;
)


hasZeroRoot = method();

hasZeroRoot (RingElement) :=(pol)->
(
    rng := ring pol;
    homVar:=homogenVariable rng;
    commVar:=commonVariable rng;
    hPol:= homogenize(pol,homVar);
    return (sub(value hPol,{homVar=>1_rng,commVar=>0_rng})==0);
)

hasOneRoot = method();
hasOneRoot(RingElement) := (pol)->
(
    rng := ring pol;
    homVar:=homogenVariable rng;
    commVar:=commonVariable rng;
    hPol:= homogenize(pol,homVar);
    return (sub(value hPol,{homVar=>1_rng,commVar=>1_rng})==0);
)
hasInfinityRoot = method();

hasInfinityRoot (RingElement) :=(pol)->
(
    rng := ring pol;
    homVar:=homogenVariable rng;
    commVar:=commonVariable rng;
    --assert(pol==homogenize(pol,homVar)); -- will always fail if only a polynomial factor is given.
    return (sub(value pol,{homVar=>0_rng,commVar=>1_rng})==0);
)

hasNormalizedRoot = method();
hasNormalizedRoot(RingElement) := (pol)->
(
    return (hasInfinityRoot(pol) or hasOneRoot(pol) or hasZeroRoot(pol) );
)

getNormalizedRootCheck = method();
getNormalizedRootCheck(RingElement) := (pol)->
(
    assert( hasNormalizedRoot(pol) );
    if (hasInfinityRoot(pol)) then 
        return hasInfinityRoot;
    if (hasOneRoot(pol)) then 
        return hasOneRoot;
    if (hasZeroRoot(pol)) then 
        return hasZeroRoot;
)


------------------------------------------------


getCoordinatesFromDeg1Factor= method();
getCoordinatesFromDeg1Factor (RingElement,PolynomialRing) := (fact,rng)->
(
  assert (ring fact===rng);
  assert (rng#?"commonVariable");
  assert (rng#?"homogenVariable");
  homogenizedFact := homogenize(fact,homogenVariable rng );
  assert( (degree homogenizedFact)#0 == 1);
  firstCoordinate := last coefficients (homogenizedFact, Monomials=>{commonVariable rng });
  secondCoordinate := last coefficients (homogenizedFact, Monomials=>{homogenVariable rng});
  return vector {firstCoordinate,secondCoordinate};
)



-- new Type RFSPolynomialInfo?

RFSPolynomialInfo = new Type of MutableHashTable;

new RFSPolynomialInfo from MutableHashTable := (A,mht)->
(
    assert( mht#?"pol");
    assert( mht#?"factors");
    --assert( mht#?"factorsByExponent");

     assert(class mht#"factors"===Product);
    --print (mht#"pol");
    --print (parent class (mht#"pol"));
    --print (parent ring (mht#"pol"));
    assert(parent class mht#"pol" === RingElement);
    assert( class ring mht#"pol" === PolynomialRing);    
    return mht;
)

createPolynomialInfo= method()
createPolynomialInfo  (RingElement):= (relem)->
(
    mht:= new MutableHashTable;
    mht#"pol"=relem;
    mht#"factors"=factor relem;
    --mht#"factorsByExponent"=factor relem;
    --mht#"factorsByExponent" = new MutableHashTable;
    --apply(mht#"factors",fact->( (mht#"factorsByExponent")#(fact#1)= fact#0 ));
    return new RFSPolynomialInfo from mht;
)

value (RFSPolynomialInfo)  := RingElement => (polInfo)->
(
    return value polInfo#"factors";
)

degree (RFSPolynomialInfo)  := ZZ => (polInfo)->
(
    return (degree polInfo#"pol")#0;
)


-- example: getRootExponent(polInfo, hasInfinityRoot)
-- fkt z. Zt. nicht notwendung 
getRootExponent = method();
getRootExponent (RFSPolynomialInfo, Thing) :=(polInfo, hasRootCheckMethod )->
(
    for fac in polInfo#"factors" do
    (
        if (hasRootCheckMethod(value fac) ) then 
            return fac#1;
    );
    return 0;
)



-- todo polynomialInfo: nicht "pol" sondern nur "factors" speichern?
sortFactorsByExponent = method();
sortFactorsByExponent  (RFSPolynomialInfo)  := HashTable => (polInfo)->
(
     result := new MutableHashTable;
     apply(polInfo#"factors",fact->( result#(fact#1) = fact#0 ));
     return new HashTable from result;
)

sortFactorsByExponent  (RingElement)  := HashTable => (pol)->
(
     result := new MutableHashTable;
     apply(factor pol,fact->( result#(fact#1) = fact ));
     return new HashTable from result;
)


-- fusch => factorsByExponent als Funktion?
update = method()
update (RFSPolynomialInfo)  := RFSPolynomialInfo=> (polInfo)->
(
     polInfo#"factors"=factor polInfo;
     polInfo#"factorsByExponent" = new MutableHashTable;
     apply(polInfo#"factors",fact->( (polInfo#"factorsByExponent")#(fact#1)= fact#0 ));
)

-- precondition: 
RFSPolynomialInfo == RFSPolynomialInfo := (x,y)->
(
    rng := ring x#"pol";
    rng2 :=ring y#"pol";
    if  (char rng != char rng2) then return false;
    if  (#(gens rng) != #(gens rng2)) then return false;
    --
    currPolynomialDegree := (degree x#"pol")#0;
    if ( currPolynomialDegree != (degree y#"pol")#0) then return false;

    assert (commonVariable rng=!=null);
    assert (homogenVariable rng=!=null);
    --
    srcMonomials := apply(currPolynomialDegree+1, exponent->((homogenVariable rng)^exponent*(commonVariable rng)^(currPolynomialDegree-exponent)));
    matrix1 := value toString last coefficients(x#"pol",Monomials=>srcMonomials);
    srcMonomials = apply(currPolynomialDegree+1, exponent->((homogenVariable rng2)^exponent*(commonVariable rng2)^(currPolynomialDegree-exponent)));
    matrix2 := value toString last coefficients(y#"pol",Monomials=>srcMonomials);
    return (matrix1==matrix2);
)


--#todo: bug entdeckt: wenn polInfo#"factors" nur einen Faktor enthält, ist es kein Produkt!
findDegOneFactorWithHighestExponent=method();
findDegOneFactorWithHighestExponent (RFSPolynomialInfo) := Power => (polInfo)->
(
  destPolFact := null;
  for polFac in factor value polInfo#"factors" do
  (
    assert(class polFac===Power);
    if ((degree polFac#0)#0==1 and (destPolFact===null or destPolFact#1<polFac#1)) then
      destPolFact = polFac;
  );
 for polFac in factor value polInfo#"factors" do
  (
    if ((degree polFac#0)#0==0 and (destPolFact=!=null)) then
    (
        assert(polFac#1==1);
     -- destPolFact = new Power from (destPolFact#0*polFac#0,destPolFact#1);
    )
  );
  return destPolFact;
)


findDegOneFactorWithGivenExponent=method();
findDegOneFactorWithGivenExponent (RFSPolynomialInfo,ZZ) := Power => (polInfo,exponent)->
(
  destPolFact := null;
  for polFac in factor value polInfo#"factors" do
  (
    assert(class polFac===Power);
    if ((degree polFac#0)#0==1 and (polFac#1==exponent)) then
      destPolFact = polFac;
  );
 for polFac in factor value polInfo#"factors" do
  (
    if ((degree polFac#0)#0==0 and (destPolFact=!=null)) then
    (
        assert(polFac#1==1);
     -- destPolFact = new Power from (destPolFact#0*polFac#0,destPolFact#1);
    )
  );
  return destPolFact;
)


deepCopy (RFSPolynomialInfo) := (rfsPolInfo)->
(
  rfsPolInfoCopy := new MutableHashTable;
  for key in keys rfsPolInfo do
    rfsPolInfoCopy#key = copy rfsPolInfo#key;
  --# rfsPolInfoCopy#"factors"= factor value rfsPolInfoCopy#"factors"; -- TODO this fixes the bug (rfsPolInfoCopy#"factors" is power and not product), but the bug is caused elsewere! P.S. and also introduces a new bug!
  rfsPolInfoCopy#"factors" = copy rfsPolInfoCopy#"factors";
  return new RFSPolynomialInfo from rfsPolInfoCopy;
)


hasOneRoot (RFSPolynomialInfo) :=(polinfo)->
(   
    return hasOneRoot(polinfo#"pol")
)
hasZeroRoot (RFSPolynomialInfo) :=(polinfo)->
(   
    return hasZeroRoot(polinfo#"pol")
)
hasInfinityRoot (RFSPolynomialInfo) :=(polinfo)->
(   
    return hasInfinityRoot(polinfo#"pol")
)


removeConstantFactorInPlace = method();

removeConstantFactorInPlace(RFSPolynomialInfo):=(rfsInfo)->
(
    result:=null;
    factList := {};
    for fac in rfsInfo#"factors" do
    (
        if ((degree fac#0)#0!=0 ) then 
        (
            factList= factList | {fac}     ;
        );
    );
    rfsInfo#"factors" = new Product from factList;
    rfsInfo#"pol"= value rfsInfo#"factors";
)

hasConstantFactors = method();
hasConstantFactors(RFSPolynomialInfo):=(rfsInfo)->
(
    for fac in rfsInfo#"factors" do
    (
        if ((degree fac#0)#0==0 and fac#0!=1 ) then
        --if ((degree fac#0)#0==0 ) then  
            return true;
    );
    return false;
)
 


RFSPolynomialTuple = new Type of MutableList;


new RFSPolynomialTuple from Thing   := (parType,parList)->
(
    --assert(false);
   return new RFSPolynomialTuple from (new MutableList from parList);
)

--allow inconsistent PolynomialTuple or not?
new RFSPolynomialTuple from MutableList   := (parType,parList)->

(
  --print "new RFSPolynomialTuple called";
  --apply(parList,elem->(print elem));

  apply(parList,elem->(assert(class elem===RFSPolynomialInfo )));
  --apply(parList,elem->(assert(degree elem== (degree parList#0) )));

  return parList;

)



deepCopy (RFSPolynomialTuple) := RFSPolynomialTuple => (polTuple)->

(

  tmpRes := new MutableList;

  for pos in 0..#polTuple-1 do

    tmpRes#pos = deepCopy( polTuple#pos);

  assert(#tmpRes==#polTuple);

  return new RFSPolynomialTuple from tmpRes;  

)


factors=method();

factors (RFSPolynomialTuple) := RFSPolynomialTuple => (polTuple)->

(
    return polTuple#"factors";
)

getFactors=method();
getFactors (RFSPolynomialTuple) := RFSPolynomialTuple => (polTuple)->

(
    return factors polTuple;
)


checkConsistency=method();
checkConsistency (RFSPolynomialTuple) := RFSPolynomialTuple => (polTuple)->

(
    assert(value polTuple#"factors"== polTuple#"pol");
    return ;
)

createPolynomialTuple=method();

createPolynomialTuple (ZZ, PolynomialRing) := RFSPolynomialTuple => (polSetSize, rng)->

(

  --polynomialTuple := new MutableHashTable; -- a List/HastTable is sufficient; we do not need Mutable.

  polynomialTuple := for currPos in 0..polSetSize-1 list 

  (

      currPolynomialInfo := new MutableHashTable;

      currPolynomialInfo#"pol" = 1_rng;

      currPolynomialInfo#"factors" = new Product from {new Power from {1_rng, 1} };

      new RFSPolynomialInfo from currPolynomialInfo

  );

  return new RFSPolynomialTuple from polynomialTuple;

)




deepCopy (RFSPolynomialTuple) := RFSPolynomialTuple => (polTuple)->

(

  tmpRes := new MutableList;

  for pos in 0..#polTuple-1 do

    tmpRes#pos = deepCopy( polTuple#pos);

  assert(#tmpRes==#polTuple);

  return new RFSPolynomialTuple from tmpRes;  

)




char (RFSPolynomialTuple) := ZZ=> (polTuple)->
(
    characteristic:=null;
    for polInfo in polTuple do
        if (characteristic===null) then
            characteristic = char ring polInfo#"pol"
        else
            assert( characteristic == char ring polInfo#"pol");
   return characteristic;   
)

ring (RFSPolynomialTuple) := ZZ=> (polTuple)->
(
    rng:=null;
    for polInfo in polTuple do
        if (rng===null) then
            rng =   ring polInfo#"pol"
        else
        (
            assert( rng ===   ring polInfo#"pol");
        );
   return rng;   
)


removeConstantFactorInPlace (RFSPolynomialTuple) :=(polTuple)->
(
    assert(#polTuple>0);
    rng := ring polTuple#0#"pol";
    for pos in 0..#polTuple-1 do
    (
        polTuple#pos#"pol" = homogenize (polTuple#pos#"pol" ,homogenVariable rng);
        polTuple#pos#"factors"= factor polTuple#pos#"pol";
        removeConstantFactorInPlace( polTuple#pos);
    );
    return;
)



------------------------------------------------------

RFSNormalizationRule = new Type of MutableHashTable;


new RFSNormalizationRule from MutableHashTable := (A,mht)->
(
    assert( mht#?"polFactorExponent");
    assert( mht#"polFactorExponent"===null or ( class mht#"polFactorExponent"===ZZ ));
    if (mht#"polFactorExponent"=!=null ) then assert( mht#"polFactorExponent">0);
    
    assert( mht#?"whichPolynomial");
    
    assert( mht#?"value");
    
    assert( mht#?"applied");
    assert( class mht#"applied" ===Boolean);
    
    return mht;
)


--internalCreateNormalizationRule = method();
--internalCreateNormalizationRule (ZZ,Thing,RingElement,Boolean) := (polFactorExponent,whichPolynomial,value, applied) ->
internalCreateNormalizationRule = (polFactorExponent,whichPolynomial,value, applied) ->
(
  mht := new MutableHashTable;
  --
  mht#"polFactorExponent"   = polFactorExponent;
  mht#"whichPolynomial"     = whichPolynomial;
  mht#"value"           = value;
  mht#"applied"         = applied;
  
  return new RFSNormalizationRule from mht;
)
 


createNormalizationRule = method (Options=>{ "polFactorExponent"       => null , 
                                            "whichPolynomial"  => null, "applied"=>false})
                                            
createNormalizationRule (RingElement) := RFSNormalizationRule => opts -> (value)->
(
  return internalCreateNormalizationRule( opts#"polFactorExponent", opts#"whichPolynomial", value, opts#"applied");
)
createNormalizationRule (InfiniteNumber) := RFSNormalizationRule => opts -> (value)->
(
 return internalCreateNormalizationRule( opts#"polFactorExponent", opts#"whichPolynomial", value, opts#"applied");
)

createNormalizationRule (ZZ) := RFSNormalizationRule => opts -> (value)->
(
 return internalCreateNormalizationRule( opts#"polFactorExponent", opts#"whichPolynomial", value, opts#"applied");
)
---------------------------------------------------------------------------------------------------

 
RFSNormRuleSet = new Type of MutableList;

new RFSNormRuleSet from BasicList := (A,normRuleList)->
(
    apply( normRuleList,elem->(assert(class elem===RFSNormalizationRule )));
    immutableNormRuleList := new List from normRuleList;
    apply( immutableNormRuleList,elem->(apply (immutableNormRuleList_{1..(#immutableNormRuleList-1)} , compElem->assert(class elem#"value"=!=compElem#"value" ))));
    return normRuleList;
)


deepCopy(RFSNormRuleSet):= RFSNormRuleSet => (normRuleSet)->
(
  nrsCopy := new MutableList from copy normRuleSet;
  apply(#nrsCopy,pos->(nrsCopy#pos = copy normRuleSet#pos));
  return new RFSNormRuleSet from nrsCopy;
)

size (RFSNormRuleSet) := ZZ =>(normRuleList)->
(
    return #normRuleList;
)

-- precond: values are different for all normalization rules!
normalizationWasApplied = method();
normalizationWasApplied (RFSNormRuleSet, Thing) := Boolean => (normalizationRuleSet, value)->
(
  assert((class value===RingElement) or (class value===InfiniteNumber));
  for normRule  in normalizationRuleSet do
  (
    if (normRule#"value"===value) then
    (
      return (normRule#"applied");
    )
  );
  return false;
)





infinityNormalizationWasApplied = method();
infinityNormalizationWasApplied (RFSNormRuleSet ) := Boolean => (normalizationRuleSet)->
(
    return normalizationWasApplied(normalizationRuleSet,infinity);
)

createStrictNormalizationRuleSet =method();
createStrictNormalizationRuleSet (List) := (factorExponentList)->
(
    assert(#factorExponentList==3);

    normValues := getDefaultNormalizationOrder();
    -- todo: define value order (infinity,0,1) in one centralized place! 
    apply(factorExponentList, el->( assert(el>0); assert(class el===ZZ);));
    firstRule := createNormalizationRule(normValues#0, "whichPolynomial"=>0, "polFactorExponent"=>factorExponentList#0);
    secondRule := createNormalizationRule( normValues#1, "whichPolynomial"=>1, "polFactorExponent"=>factorExponentList#1);
    thirdRule := createNormalizationRule( normValues#2, "whichPolynomial"=>2, "polFactorExponent"=>factorExponentList#2);

    return new RFSNormRuleSet from {firstRule,secondRule,thirdRule}
)


createStrictNormalizationRuleSet (Array) := (factorExponentList)->
(
    return createStrictNormalizationRuleSet(new List from factorExponentList);
)

------------------------------------------------------------------------------------------

getDegreeOneFactors=method();
getDegreeOneFactors (RFSPolynomialTuple,RFSNormRuleSet) := (polTuple, normRules)->
(
    assert(size normRules==3);
    currFactor := null;
    tmpFactorList := {} ;

    for normRule in normRules do
    (
          assert(normRule#"whichPolynomial"=!=null);
          assert(normRule#"polFactorExponent"=!=null);
          print (normRule#"whichPolynomial");
          print (normRule#"polFactorExponent");
          currFactor = findDegOneFactorWithGivenExponent(polTuple#(normRule#"whichPolynomial"), normRule#"polFactorExponent" );
          assert(currFactor=!=null);
          tmpFactorList = tmpFactorList |{currFactor};
    );
    return tmpFactorList;
)


getDegreeOneFactors (RFSPolynomialTuple,ZZ) := (polTuple, numOfFactors)->
(
  assert(numOfFactors>=0);
  currFactor := null;
  tmpFactor := null; --is a pair of pairs (Power,  polynomialId)
  tmpFactorList := {} ;
   seq := 0..#polTuple-1;
   whichPolynomial := null;
  for factorNr in 0..numOfFactors-1 do
  (
    tmpFactor=null;
   
    for pos in seq do
    (
      currFactor = findDegOneFactorWithHighestExponent(polTuple#pos);
      --print currFactor;
      --print tmpFactor#1;
      --  print currFactor#1;  
    if (currFactor=!=null) then 
      if (tmpFactor===null or tmpFactor#1<currFactor#1) then 
      (
        tmpFactor = currFactor;
        whichPolynomial=pos;
      );
    );
   if (tmpFactor=!=null) then
   (
  
    tmpFactorList= tmpFactorList |{tmpFactor};
    seq=delete (whichPolynomial,seq);
   );
  );
  return tmpFactorList;
)

-- todo: simplify?
internalComputeNormalizationMap = (factorlist,normRules)->
(
    localFactorlist:=factorlist;
  --note: factorlist expected in order as normRules, but has to be in order  infinity, zero, one.
  if (normRules=!=null) then 
    (
        assert(#factorlist==#normRules);
        localFactorlist= {};
         for pos in 0..#factorlist-1 do
         (
                if (normRules#pos#"value"==infinity) then 
                    localFactorlist=localFactorlist | {factorlist#pos};
         );
         for pos in 0..#factorlist-1 do
         (
                if (normRules#pos#"value"==0) then 
                    localFactorlist=localFactorlist | {factorlist#pos};
         );
         for pos in 0..#factorlist-1 do
         (
                if (normRules#pos#"value"==1) then 
                 localFactorlist=localFactorlist | {factorlist#pos};
         );
         assert(#localFactorlist==#factorlist);
    );


  assert(#factorlist <= 3);
  rng := null;
  firstFactor := null;
  firstCoord := null;
  secondFactor := null;
  secondCoord := null;
  thirdFactor := null;
  thirdCoord := null;
  result := null;
  resMap := null;
  mat:=null;
  rhs:=null;    

  if (#factorlist==3) then
  (
    --unknowns: m,n,o,p ,alpjha,beta with Transformation matrix { {m,n},{o,p} }
    firstFactor = localFactorlist#1#0;
    --print firstFactor;
    rng= ring firstFactor;
    assert((degree firstFactor)#0 == 1);
    mat = mutableMatrix(ring firstFactor,6,6);
    firstCoord= getCoordinatesFromDeg1Factor(firstFactor, rng);
    --print "firstCoord" ;
    --print firstCoord ;
    
    -- m*x1+ o*y1-alpha = 0;
    mat_(0,0) = firstCoord_(0); -- m*x1;
    mat_(0,2) = firstCoord_(1); -- o*y1;
    mat_(0,4) = -1_rng; -- -alpha;
    -- n*x1+ p*y1=0;
    mat_(1,1) = firstCoord_(0); -- n*x1;
    mat_(1,3) = firstCoord_(1); -- p*y1;
    
    secondFactor = localFactorlist#0#0;
    secondCoord= getCoordinatesFromDeg1Factor(secondFactor, rng);
     -- m*x2+ o*y2 = 0;
    mat_(2,0) = secondCoord_(0); -- m*x2;
    mat_(2,2) = secondCoord_(1); -- o*y2;
     -- n*x2+ p*y2 -beta = 0;
    mat_(3,1) = secondCoord_(0); -- m*x2;
    mat_(3,3) = secondCoord_(1); -- o*y2;
    mat_(3,5) = -1_rng; -- -beta;
     
    thirdFactor = localFactorlist#2#0;
    thirdCoord= getCoordinatesFromDeg1Factor(thirdFactor, rng);
     -- m*x2+ o*y2 = 0;
    mat_(4,0) = thirdCoord_(0); -- m*x2;
    mat_(4,2) = thirdCoord_(1); -- o*y2;
     -- n*x2+ p*y2 -beta = 0;
    mat_(5,1) = thirdCoord_(0); -- m*x2;
    mat_(5,3) = thirdCoord_(1); -- o*y2;
  -- print {(matrix mat)};
   --print (rank matrix mat);
   -- print ("rank = "| rank matrix mat);
   -- if (rank matrix mat==5) then
   --     print (matrix mat);

     rhs = vector{ 0_rng, 0_rng, 0_rng, 0_rng, 1_rng, -1_rng};
   -- print {(matrix mat)^-1};
    result = (matrix mat)^-1 * rhs;
  
    resMap = map(rng,rng,matrix{{  (commonVariable rng)*result_(0)+ (homogenVariable rng)*result_(1),
                                (commonVariable rng)*result_(2)+(homogenVariable rng)*result_(3)
                            }}
                );
    --print result;
    return resMap;
  );
   if (#factorlist==2) then
  (
   
    --unknowns: m,n,o,p ,alpjha,beta with Transformation matrix { {m,n},{o,p} }
    firstFactor = localFactorlist#0#0;
   -- print firstFactor;
    rng= ring firstFactor;
    assert((degree firstFactor)#0 == 1);
    mat = mutableMatrix(ring firstFactor,4,4);
    firstCoord= getCoordinatesFromDeg1Factor(firstFactor, rng);
    --print "firstCoord" ;
    --print firstCoord ;
    
    -- m*x1+ o*y1-alpha = 0;
    mat_(0,0) = firstCoord_(0); -- m*x1;
    mat_(0,2) = firstCoord_(1); -- o*y1;
  
    -- n*x1+ p*y1=0;
    mat_(1,1) = firstCoord_(0); -- n*x1;
    mat_(1,3) = firstCoord_(1); -- p*y1;
    
    secondFactor = localFactorlist#1#0;
    secondCoord= getCoordinatesFromDeg1Factor(secondFactor, rng);
     -- m*x2+ o*y2 = 0;
    mat_(2,0) = secondCoord_(0); -- m*x2;
    mat_(2,2) = secondCoord_(1); -- o*y2;
     -- n*x2+ p*y2 -beta = 0;
    mat_(3,1) = secondCoord_(0); -- m*x2;
    mat_(3,3) = secondCoord_(1); -- o*y2;
 
     
    --print ("rank = "| rank matrix mat);
     rhs = vector{ 1_rng, 0_rng, 0_rng, 1_rng};
    --print {(matrix mat)^-1};
    result = (matrix mat)^-1 * rhs;
    
    resMap = map(rng,rng,matrix{{  (commonVariable rng)*result_(0)+(homogenVariable rng)*result_(1),
                                (commonVariable rng)*result_(2)+(homogenVariable rng)*result_(3)
                            }}
                );
    --print result;
    return resMap;
  );
   if (#factorlist==1) then
  (
      firstFactor = localFactorlist#0#0;
       rng= ring firstFactor;
      firstCoord= getCoordinatesFromDeg1Factor(firstFactor, rng);
      if (firstCoord_(0)==0) then 
        firstCoord= (1_rng,firstCoord_(1));
      if (firstCoord_(1)==0) then 
        firstCoord=(firstCoord_(0),1_rng);
      resMap = map(rng,rng,matrix{{  (commonVariable rng)*(firstCoord_(0)^-1) ,
                                 (homogenVariable rng) *(firstCoord_(1)^-1)
                            }}
                );
    --print result;
    return resMap;
  ); 
  rng= ring localFactorlist#0#0;
  return map(rng,rng,matrix{{  (commonVariable rng)  ,
                                 (homogenVariable rng)  
                            }});
)

computeNormalizationMap=method();
computeNormalizationMap (List) := (factorlist)->
(
    
    for permutation in permutations factorlist do 
    (
        try 
        ( 
            return internalComputeNormalizationMap(permutation,null) 
         )
        then ( )
        else ( );
    );
    assert(false);
)

computeNormalizationMap (List,Thing) := (factorlist, normRules)->
(  
    assert(normRules===null or class normRules===RFSNormRuleSet);
        try 
        ( 
            return internalComputeNormalizationMap(factorlist,normRules) 
         )
        then ( )
        else ( );
    assert(false);
)

computeNormalizationMapDebug = (factorlist)->
(
    for permutation in permutations factorlist do 
    (
       -- try 
        --( 
            return internalComputeNormalizationMap(permutation) 
        -- )
        --then ( )
       -- else ( );
    );
    assert(false);
)



computeNormalisationMap = method();

computeNormalisationMap (RFSPolynomialTuple, Thing) :=(polTuple,normRules)->
(
    assert(normRules===null or class normRules===RFSNormRuleSet);
    assert(#polTuple>0);
    degOneFactors:=null;
    if (normRules=!=null) then 
    (
        degOneFactors = getDegreeOneFactors(polTuple,normRules);
        print "degOneFactors";
        print degOneFactors;
    )
    else
      degOneFactors = getDegreeOneFactors(polTuple,3);
  nmap := computeNormalizationMap(degOneFactors,normRules);
 return nmap;
)

makePolInfoFactorsMonic := method();

makePolInfoFactorsMonic(RFSPolynomialInfo):=(polInfo)->
(
    rng:=ring  polInfo#"pol";
    correction:=1_rng;
    factorList:={};

    for currFactor in polInfo#"factors" do
    (
        currPolynomialDegree := (degree currFactor#0)#0;

        if ( currPolynomialDegree ==0) then
        (
            correction=correction*(value currFactor);
            continue;
        );
        currPolynomialExp := currFactor#1;
            srcMonomials := apply(currPolynomialDegree+1, exponent->((homogenVariable rng)^exponent*(commonVariable rng)^(currPolynomialDegree-exponent)));
            currCoefficients := last coefficients(currFactor#0,Monomials=>srcMonomials);
            if ( currCoefficients_0_0!=0) then 
            (
                nweFactor:=new Power from {((currCoefficients_0_0)^-1)*currFactor#0,currPolynomialExp};
                print "nweFactor";
                print nweFactor;
                correction= correction*((currCoefficients_0_0)^-1)^currPolynomialExp;
                print "correction";
                print correction;
                factorList=factorList| { nweFactor } ;
            )
            else
            (
                factorList=factorList| { new Power from {currFactor#0, currPolynomialExp } } ;
            )
    );
    factorList = factorList| { new Power from {correction,1} };
    tmpFactors :=new Product from factorList;

     if (value tmpFactors != value polInfo#"factors") then
    (
        print( "-- warning: 'makePolInfoFactorsMonic' changed polInfo");
    );
            

    polInfo#"factors"= tmpFactors;
    polInfo#"pol"= value tmpFactors;
)

makePolTupleFactorsMonic = method();
makePolTupleFactorsMonic (RFSPolynomialTuple) :=(polTuple)->
(
 -- nun: ich moechte, dass jeder faktor monisch in t ist. 
    for polInfo  in polTuple  do
    (
        makePolInfoFactorsMonic( polInfo );
       
    );
)


normalizePolynomialTupleInPlace = method();
normalizePolynomialTupleInPlace (RFSPolynomialTuple, Thing) :=(polTuple,normRules)->
(
  assert(normRules===null or class normRules===RFSNormRuleSet);
  assert(#polTuple>0);
  nmap := computeNormalisationMap(polTuple,normRules); 
  rng := ring polTuple#0#"pol";
  for pos in 0..#polTuple-1 do
  (
   polTuple#pos#"pol" = homogenize (polTuple#pos#"pol" ,homogenVariable rng);
    polTuple#pos#"pol" = nmap polTuple#pos#"pol";
    polTuple#pos#"factors"= factor polTuple#pos#"pol";
    makePolInfoFactorsMonic(polTuple#pos);  
    removeConstantFactorInPlace( polTuple#pos);
  );
  return;
)




------------------------
 
 -- Parameter types: destPolynomial: string;multiplicityStructure: a list of exponents or a Partition?

PolFactorConstructionRule = new Type of HashTable; -- rename to polFactor


PolFactorBlueprint = new Type of HashTable; -- rename to polFactor

new PolFactorBlueprint from HashTable := (A,polynomialConstructionRule)->
(
    assert( polynomialConstructionRule#?"polFactorExponent" ); 
    assert( polynomialConstructionRule#?"polFactorDegree" ); 
    assert( polynomialConstructionRule#?"whichPolynomial" );
    
    assert( polynomialConstructionRule#"polFactorExponent">0 );
    assert( polynomialConstructionRule#"polFactorDegree">=0 ); 
    
    return polynomialConstructionRule;
)


-- PolFactorConstructionRule has only semantic difference to PolFactorBlueprint 
new PolFactorConstructionRule from HashTable := (A, prePolConstRule )->
(
    
    return new PolFactorBlueprint from prePolConstRule;
)



 createPolFactorConstructionRules=(partition, destPolynomial, polFactorExponent)->
 (
    result := apply(new List from partition, currDeg->(
                                  tmpres := new MutableHashTable;
                                  tmpres#"polFactorDegree"=currDeg;
                                  tmpres#"whichPolynomial"=destPolynomial;
                                  tmpres#"polFactorExponent"=polFactorExponent;
                                  new PolFactorConstructionRule from tmpres
                              )
    );
    --print "createPolFactorConstructionRules";
    --print result;
    
    return result;
 )

createPolFactorBlueprint = (currExponent, currDegree, destPolynomial)->
(
      prePolConstRule := new MutableHashTable ;
        prePolConstRule#"polFactorExponent" = currExponent;
        prePolConstRule#"polFactorDegree" =  currDegree;
        prePolConstRule#"whichPolynomial" = destPolynomial;
    --  return  new PolFactorConstructionRule from prePolConstRule;
    return  new PolFactorBlueprint from prePolConstRule;
)


PolynomialConstructionRuleSet = new Type of MutableList;

createPolFactorBlueprintList = method();
 createPolFactorBlueprintList (Shape, ZZ) := (shape, destPolynomial)->
 (
    if ( #(shape#"shape") == 0 ) then return {};
    polFactorBlueprintList := {};
    currExponent := shape#"shape"#0;
    currDegree := 1;
    currPos := 1 ;
    tmpEntry := null;
    --check precondition: shape#"shape" entries are sorted desc.
    assert(rsort exponents shape == exponents shape);
    while (currPos<#(shape#"shape")) do
    (
      if ((shape#"shape")#currPos<currExponent) then
      (
        tmpEntry = createPolFactorBlueprint( currExponent,currDegree, destPolynomial );
        polFactorBlueprintList = polFactorBlueprintList | { tmpEntry };
        currDegree = 0;
      );
      currExponent = (shape#"shape")#currPos;
      currDegree = currDegree + 1;
      currPos = currPos + 1 ;
    );
    tmpEntry = createPolFactorBlueprint( currExponent,currDegree, destPolynomial );
    polFactorBlueprintList = polFactorBlueprintList | { tmpEntry };
    return polFactorBlueprintList;
 )
 
 --------------------------------------------------------------------------------------


PolynomialConstructOptions  = new Type of MutableHashTable;

-- todo: separate normal options and debug options?
new PolynomialConstructOptions  := (A)->
(
    constructOptions := new MutableHashTable;
    constructOptions#"setLambdaToOne"= false;   --debug option
    constructOptions#"computeFullShape"= false; --debug option?
    constructOptions#"parallelize"= false;
    constructOptions#"minChar"=2;
    constructOptions#"maxChar"=null;
    constructOptions#"parallelize"=false;
    constructOptions#"softExampleLimit"=1;
    constructOptions#"earlyBreak"=false;
    constructOptions#"reorderShape"=false;
     constructOptions#"normalizationRuleSet"=null;
    constructOptions#"onlyNormalizableExamples"=false;
    return constructOptions;  
)

-- todo: problem, wenn man 2x schreibt irgendwas=method();
-- todo: asserts in Fehlermeldungen umwandeln.
checkAndCorrectPolynomialConstructOptionsConsistency = method();
checkAndCorrectPolynomialConstructOptionsConsistency(Thing):=(options)->
(
   if (not options#"minChar">0) then 
        error("PolynomialConstructOptions.minChar must be >1");

    if ( options#"maxChar"=!=null ) then 
    (
        assert(options#"maxChar">=options#"minChar");
          
    )
    else
    (
         if ( options#"softExampleLimit"===null ) then 
         (
            error("PolynomialConstructOptions.softExampleLimit must be set  if maxChar is not!" );
         );
    );

    assert(options#"softExampleLimit"===null or options#"softExampleLimit">0);

    return;
)


checkAndCorrectConsistency:=method();
checkAndCorrectConsistency(PolynomialConstructOptions):=(options)->
(
    return checkAndCorrectPolynomialConstructOptionsConsistency(options);
)

new PolynomialConstructOptions from MutableHashTable := (A,mht)->
(
    
  assert(mht#?"computeFullShape");
  assert(class mht#"computeFullShape"===Boolean);
  
  assert(mht#?"setLambdaToOne");
  assert(class mht#"setLambdaToOne"===Boolean);
  
  assert(mht#?"parallelize");
  assert(class mht#"parallelize"===Boolean);

  assert(mht#?"earlyBreak");
  assert(class mht#"earlyBreak"===Boolean);

  assert(mht#?"reorderShapeList");
  assert(class mht#"reorderShapeList"===Boolean);


    assert(mht#?"minChar");
    assert(mht#"minChar"=!=null and (class mht#"minChar"===ZZ) and mht#"minChar">=0);

    assert(mht#?"maxChar");
      assert(mht#"maxChar"===null or (class mht#"maxChar"===ZZ and mht#"maxChar">=0));

   assert(mht#?"normalizationRuleSet");
      assert(mht#"normalizationRuleSet"===null or (class mht#"normalizationRuleSet"===RFSNormRuleSet ));


    assert(mht#?"softExampleLimit");
    assert(mht#"softExampleLimit"===null or (class mht#"softExampleLimit"===ZZ) and mht#"softExampleLimit">0);
 

    assert(mht#?"onlyNormalizableExamples");
    assert(class mht#"onlyNormalizableExamples"===Boolean);

   checkAndCorrectPolynomialConstructOptionsConsistency(mht);
  return mht;  
)


defaultNormalizationRuleSet = ()->
(
    normalizationRuleZero := createNormalizationRule(0, "polFactorExponent"=>null, "whichPolynomial"=>null );
    normalizationRuleOne  := createNormalizationRule(1, "polFactorExponent"=>null, "whichPolynomial"=>null );
    normalizationRuleInfinity := createNormalizationRule( infinity, "polFactorExponent"=>null, "whichPolynomial"=>null );
  
    normalizationRuleSet := new RFSNormRuleSet from  {normalizationRuleInfinity, normalizationRuleZero, normalizationRuleOne} ;
    return normalizationRuleSet;
)

createPolynomialConstructOptions=method(
 Options=>{
                                        "reorderShapeList"=>false,
                                       "minChar"=>2,
                                       "maxChar"=>null,
                                        "onlyNormalizableExamples"=>true,
                                        "normalizationRuleSet"=>defaultNormalizationRuleSet(),
                                       
                                        "softExampleLimit"=>1,
                                      
                                        "earlyBreak"=>false,
                                        "parallelize"=>false
                                    }
    );

-- dummy because it is hard to define a method without parameters...
createPolynomialConstructOptions (Thing) := opts->(dummy)->
(
    constructOptions := new MutableHashTable;
    -- 
    -- not set by the parameters - only "by hand"
    constructOptions#"setLambdaToOne"= false;
    constructOptions#"computeFullShape"= true;
    -- 
    constructOptions#"reorderShapeList"=opts#"reorderShapeList";

    constructOptions#"minChar"=opts#"minChar";


    constructOptions#"maxChar"=opts#"maxChar";

    constructOptions#"softExampleLimit"=opts#"softExampleLimit";

    constructOptions#"earlyBreak"=opts#"earlyBreak"; -- breaks as long as softExampleLimit are computed. Otherwise continues until all examples for the current characteristic are computed.
    
   constructOptions#"onlyNormalizableExamples"=opts#"onlyNormalizableExamples";   

    constructOptions#"parallelize"= opts#"parallelize";


    constructOptions#"normalizationRuleSet" = opts#"normalizationRuleSet";
    assert (class constructOptions#"normalizationRuleSet"=== RFSNormRuleSet );

 

    result := new PolynomialConstructOptions from constructOptions;
    -- checkAndCorrectConsistency(result);
    return result;

)


stopConditionFulfilled= method();
stopConditionFulfilled (PolynomialConstructOptions,ZZ,ZZ) :=(constructOptions, currentCharacteristic,computedExampleCount)->
(
    
    if (constructOptions#"maxChar" =!=null and constructOptions#"maxChar" < currentCharacteristic) then 
        return true;
 
    if (constructOptions#"softExampleLimit" =!=null and constructOptions#"softExampleLimit" <= computedExampleCount) then 
        return true;


    return false;
)
--------------------------------------------------------
-- optional fuer die Zukunft: minPolyFilter.


ScalingRelations  = new Type of  MutableHashTable;

new ScalingRelations from HashTable := (A,mht)->
(
    assert(mht#?"scalingRelations");

    assert(mht#?"normalizeByFirstScalar");
    assert(Boolean===class mht#"normalizeByFirstScalar");

  

    assert(mht#?"getRestrictingEquations");

    return mht;
)

--#todo: eventuelles problem: die scalingRelations sind zwar gleich aber in verschiedenen Ringen definiert (zz,QQ)
ScalingRelations == ScalingRelations := (scRelX,scRelY)->
(
    scalingRelationsX := scRelX#"scalingRelations";
    scalingRelationsY := scRelY#"scalingRelations";
    if (scalingRelationsX != scalingRelationsY) then 
        return false;
     if (scalingRelationsX =!=  null) then
    (
        if (#scalingRelationsX != #scalingRelationsY) then 
            return false;
        for pos in 0..#scalingRelationsX-1 do
        (
        if ( (class scalingRelationsX#pos =!= class scalingRelationsY#pos) or scalingRelationsX#pos != scalingRelationsY#pos) then
            return false;
        );
    );
    if ( scRelX#"normalizeByFirstScalar"!= scRelY#"normalizeByFirstScalar") then 
        return false;
    return true;
)

testScalingRelationsEquality = ()->
(
    sc1:=    createScalingRelations({{1,2}},false);
    sc2:=    createScalingRelations({{1,2}},false);
    sc3:=    createScalingRelations({{1,2}},true);
    sc4:=    createScalingRelations({{1,3}},false);
    --sc5:=    createScalingRelations({{1_QQ,2_QQ}},false);
    assert(sc1==sc2);
    assert(sc1!=sc3);
    assert(sc1!=sc4);
    --assert(sc1!=sc5); 
)

createPolSetFilter=method();
createPolSetFilter (ScalingRelations,Thing)  := (scalingRelationObj, normRuleList)->
(  
    assert(normRuleList===null or class normRuleList===RFSNormRuleSet);

    if (scalingRelationObj#"scalingRelations"=!=null and #scalingRelationObj#"scalingRelations">0) then
    (
        scalingMinPolList := apply(scalingRelationObj#"scalingRelations",relation->minPolyFromReImPair(relation,null) ); 
        if (normRuleList===null) then 
        (
            return createDefaultScalingFilter(scalingMinPolList, scalingRelationObj#"normalizeByFirstScalar" );
        )
        else
        (
            assert( scalingRelationObj#"normalizeByFirstScalar" == true );
           return createScalingFilter(scalingMinPolList,true, normRuleList );
        );
    )
    else
    (
        return (polSet,shapeList)->true;
    );
)

createScalingRelations=method();
createScalingRelations (Thing,Boolean)  :=(scalingRelationList, normalizeByFirstScalar)->
(
    mht := new MutableHashTable;
    mht#"scalingRelations" = scalingRelationList;
    mht#"normalizeByFirstScalar"=normalizeByFirstScalar;
  

    if (scalingRelationList=!=null and #scalingRelationList>0) then
    (
        scalingMinPolList := apply(scalingRelationList,relation->minPolyFromReImPair(relation,null)); 
        -- todo: besseren Namen für polSetFilter überlegen.
        --mht#"polSetFilter" = createDefaultScalingFilter(scalingMinPolList,normalizeByFirstScalar);
    
        mht#"getRestrictingEquations"=(scalingVariables)->
        (
            assert(#scalingVariables==#scalingRelationList+1);
            if normalizeByFirstScalar then 
                return  apply(#scalingRelationList,pos->minPolyFromReImPair(scalingRelationList#pos,scalingVariables#(pos+1)) )
            else 
                return  apply(#scalingRelationList,pos->minPolyFromReImPair(scalingRelationList#pos,scalingVariables#(pos+1)) );  
            
        );
    )
    else
    (
        mht#"getRestrictingEquations" = (scalingVariables)->{};
        --mht#"polSetFilter" = (polSet,shapeList)->true;
        
    );
    return new ScalingRelations from mht;
)

createScalingRelations (Thing)  :=(scalingRelationList)->
(
    return createScalingRelations(scalingRelationList,false);
)

minPolyFromReImPair = method();
minPolyFromReImPair (List,Thing) :=RingElement => (scalingPair,variable)->
(
    assert(#scalingPair==2);  
    a:=scalingPair#0;
    b:=scalingPair#1;
    assert(class a===ZZ or class a===QQ);
    assert(class b===ZZ or class b===QQ);
    a= sub (a,QQ);
    b= sub (b,QQ);
    aNumerator := numerator a;
    aDenominator := denominator a;
    bNumerator:= numerator b;
    bDenominator:= denominator b;

    kgv := bDenominator*aDenominator;
    localVariable:=variable;
    if (localVariable===null) then 
    (   x:=null;
        rng:=ZZ[symbol x];
       localVariable = (gens rng)#0;
    );
    if (b==0) then
           return (aDenominator*localVariable - aNumerator)   -- keine komplex-konjugierte Lösung dazunehmen, weil dann die Jacobi-Matrix für den Lösungspunkt singulär wird.
    else 
        -- idea: 0 = (x-(a+i*b))*(x-(a-i*b)) = x²+a²+b²- 2*x*a. Then kill denominators.
        return (bDenominator^2*aDenominator^2*localVariable^2 + bDenominator^2*aNumerator^2 + aDenominator^2*bNumerator^2 - 2*bDenominator^2*aDenominator*localVariable*aNumerator)
    

)


testLocality =(num)->
(
    localMHT:= new MutableHashTable;
    localMHT#"num"=num;
    --
    localMHT#"func" = ()->
    (
        return localMHT#"num";
    );
    return localMHT#"func";
)

--precondition: works only , if it is possible to apply three normalization rules.
-- todo: 1. check, if 0,1, and infinity is present after normalization.
--       2. rearrange polynomials in order infinity, 0, 1.
--       3. rearrangement should be happen in the normalization step!
--       4. normalizing belongs to the RFSPolynomialSet object
-- find out if non-fullnormalizable examples are of interest in general, e.g. for counting, etc; otherwise they could be skipped generally
-- should be constructing from nonhomogenized polynomials be possible? 

createDefaultScalingFilter=method();  
createDefaultScalingFilter (List,Boolean) := (minPolyList,normalizedByFirstScalar)->
(
    defaultScalingFilter:= new MutableHashTable;
    defaultScalingFilter#"minPolyList"= minPolyList; -- deep Copy required?

    filterMethod := method();
    filterMethod (RFSPolynomialTuple,RFSShapeList) :=  (polSet,shapeList)->
    (
        minPolyList:= defaultScalingFilter#"minPolyList";

        assert(#minPolyList==(#polSet-3)); 
        --todo: muss man hier eigentlich permutieren oder werden bei der brute force suche schon sowieso alle Möglichkeiten durchlaufen?
        for permutation in permutations new List from polSet do 
        (
            dstPermutedPolSet :=   new RFSPolynomialTuple from permutation;
            --
            if not polynomialTupleMatchesShapeList(polSet, shapeList) then 
                continue;
            dstPermutedPolSetCopy := deepCopy dstPermutedPolSet;
            removeConstantFactorInPlace(dstPermutedPolSetCopy);
            normalizePolynomialTupleInPlace(dstPermutedPolSetCopy,null);
            alphaFactors := computeAlphaFactors(dstPermutedPolSetCopy);
            assert(alphaFactors=!=null);
        
            -- wenn alphalist die Bedingungen von MinPolylist erfüllt, dann 
            -- ändere polynomialSet wie 
            scalingFilterPassed:=true;
            for alphaFactorPos in 1..#alphaFactors-1 do
            (
                currScalingFactor:= alphaFactors#alphaFactorPos;
                if (normalizedByFirstScalar) then
                    currScalingFactor=currScalingFactor*(alphaFactors#0)^-1;
                if (sub (minPolyList#(alphaFactorPos-1),matrix {{ currScalingFactor}} )!=0 ) then
                (
                        scalingFilterPassed=false;
                        break;
                );
            );
            if (scalingFilterPassed) then 
            (
                for pos in 0..#polSet-1 do
                    polSet#pos=dstPermutedPolSet#pos;
                return true;
            );
        );
        return false;
    );
    defaultScalingFilter#"filter"= filterMethod;
     return defaultScalingFilter#"filter"
)



createScalingFilter=method();  
createScalingFilter (List,Boolean,RFSNormRuleSet) := (minPolyList,normalizedByFirstScalar,normRuleList)->
(
    defaultScalingFilter:= new MutableHashTable;
    defaultScalingFilter#"minPolyList"= minPolyList; -- deep Copy required?

    filterMethod := method();
    filterMethod (RFSPolynomialTuple,RFSShapeList) :=  (polSet,shapeList)->
    (
        minPolyList:= defaultScalingFilter#"minPolyList";

        assert(#minPolyList==(#polSet-3)); 
        --todo: muss man hier eigentlich permutieren oder werden bei der brute force suche schon sowieso alle Möglichkeiten durchlaufen?
        for permutation in permutations new List from polSet do 
        (
            dstPermutedPolSet :=   new RFSPolynomialTuple from permutation;
            --
            if not polynomialTupleMatchesShapeList(polSet, shapeList) then 
                continue;

            scalingFilterPassed:=true;

            dstPermutedPolSetCopy := deepCopy dstPermutedPolSet;
            removeConstantFactorInPlace(dstPermutedPolSetCopy);
            try (normalizePolynomialTupleInPlace( dstPermutedPolSetCopy,normRuleList )) then (scalingFilterPassed=true;) else (scalingFilterPassed=false; continue;);
            alphaFactors := computeAlphaFactors(dstPermutedPolSetCopy);
            assert(alphaFactors=!=null);
        
            -- wenn alphalist die Bedingungen von MinPolylist erfüllt, dann 
            -- ändere polynomialSet wie 
         
            for alphaFactorPos in 1..#alphaFactors-1 do
            (
                currScalingFactor:= alphaFactors#alphaFactorPos;
                if (normalizedByFirstScalar) then
                    currScalingFactor=currScalingFactor*(alphaFactors#0)^-1;
                if (sub (minPolyList#(alphaFactorPos-1),matrix {{ currScalingFactor}} )!=0 ) then
                (
                        scalingFilterPassed=false;
                        break;
                );
            );
            if (scalingFilterPassed) then 
            (
                for pos in 0..#polSet-1 do
                    polSet#pos=dstPermutedPolSet#pos;
                return true;
            );
        );
        return false;
    );
    defaultScalingFilter#"filter"= filterMethod;
     return defaultScalingFilter#"filter"
)


-----------------------------------------------------------------------



RFSProblem = new  Type of HashTable;


new RFSProblem from HashTable := (A,mht)->
(
    assert(mht#?"shapeList");

    assert(mht#?"scalingRelationObj");
    assert(mht#?"normalizationRules");
    assert(RFSShapeList===class mht#"shapeList");
    assert(ScalingRelations===class mht#"scalingRelationObj");
    assert(mht#"normalizationRules"===null or class mht#"normalizationRules"===RFSNormRuleSet);
    assert( (mht#"scalingRelationObj"#"scalingRelations")===null or #(mht#"shapeList")-3==#(mht#"scalingRelationObj"#"scalingRelations") or #(mht#"scalingRelationObj"#"scalingRelations"==0 ) );

    return mht;
)

 
minCharacteristic (RFSProblem) :=(rfsProblem)->
(
    return (minCharacteristic (rfsProblem#"shapeList"));
)


--# todo: evtl ScalingRelations in ScalingConditions umbenennen
createRFSProblem=method();
createRFSProblem (RFSShapeList, Thing, ScalingRelations):=(shapeList,normalizationRuleSet, scalingRelationObj)->
(
    assert(normalizationRuleSet===null or class normalizationRuleSet=== RFSNormRuleSet);

    rfsProblem := new MutableHashTable;

    rfsProblem#"shapeList" = shapeList;

    if (normalizationRuleSet=!=null) then
    (
        assert(size normalizationRuleSet==3);
        apply(normalizationRuleSet,normrule->( assert(normrule#"polFactorExponent"=!=null and normrule#"whichPolynomial"=!=null);));
        counts:= apply(3,exp->#(select(normalizationRuleSet, (val)->(val#"whichPolynomial"==exp))));
       -- apply(counts, count->(assert(count==1);));  -- each polynomial appears only once
        -- todo : eventuappy put the commented out assert line back.

    );

    rfsProblem#"normalizationRules" = normalizationRuleSet;

    rfsProblem#"polSetFilter"= createPolSetFilter( scalingRelationObj, normalizationRuleSet );

    rfsProblem#"scalingRelationObj" = scalingRelationObj;

    
    return new    RFSProblem from rfsProblem;
)

 
createRFSProblem (RFSShapeList,ScalingRelations):=(shapeList,scalingRelationObj)->
(
    return createRFSProblem(shapeList,null,scalingRelationObj);
)

 
createRFSProblem (RFSShapeList,RFSNormRuleSet):=(shapeList,normRuleSet)->
(
    normalizeByFirstScalar :=false;
    emptyScalingRelations := createScalingRelations(null,normalizeByFirstScalar);
    return createRFSProblem(shapeList,normRuleSet,emptyScalingRelations);
)


createRFSProblem (RFSShapeList):=(shapeList)->
(
    normalizeByFirstScalar:=false;
    emptyScalingRelations:= createScalingRelations(null,normalizeByFirstScalar);
    return createRFSProblem(shapeList,emptyScalingRelations);
)

---------------------------------------------------------------------------------


-- todo: Problem: vergleich funktioniert nicht, weil Mutable?
RFSPolynomialSet = new Type of MutableHashTable;

new RFSPolynomialSet from MutableHashTable   := (parType,prePolSet)->
(
  --apply(parList,elem->(print elem));

    assert(prePolSet#?"rfsProblem");
    assert(prePolSet#?"polTuple");

    assert(prePolSet#?"point");
    assert(prePolSet#?"ideal");
    assert(prePolSet#?"equations");
    assert(prePolSet#?"unknownVariableList");
    assert(prePolSet#?"scalingVariableList");

    assert(prePolSet#?"rootList");
    assert(prePolSet#?"liftInfo");

    assert(prePolSet#?"solutionIdeal");
    assert(prePolSet#?"solutionList");

    assert(prePolSet#"rfsProblem"===null or class prePolSet#"rfsProblem"===RFSProblem);

    polTuple := prePolSet#"polTuple";

   assert(class polTuple === RFSPolynomialTuple);

    apply(polTuple,elem->(assert(class elem===RFSPolynomialInfo )));
    apply(polTuple,elem->(assert(degree elem== (degree polTuple#0) )));

  return prePolSet;
)

--# 1. hmm, deepCopy muss das problem nicht kopieren, denn das Problem bleibt gleich...
--# 2. deepCopy muss für RFSPolSet ersetzt werden...

deepCopy (RFSPolynomialSet) := RFSPolynomialSet => (polSet)->
(
  
  polTuple := polSet#"polTuple";
  tmpRes := new MutableList;
  for pos in 0..#polTuple-1 do
    tmpRes#pos = deepCopy( polTuple#pos);
  assert(#tmpRes==#polTuple);
    

  return new RFSPolynomialSet from tmpRes;  
)



createRFSPolynomialSet = method() ;
createRFSPolynomialSet( RFSProblem, RFSPolynomialTuple ) := RFSPolynomialSet => (rfsProblem, polynomialTuple)->
(
    polynomialSet := new MutableHashTable;
    polynomialSet#"polTuple" = polynomialTuple;
    polynomialSet#"rfsProblem" = rfsProblem;

    --1. available after calling createLiftInputData
        polynomialSet#"point" = null; 
        polynomialSet#"ideal" = null; -- todo: eventually rename to 'idealProblemFormulation' 
        polynomialSet#"equations" = null;  
        polynomialSet#"unknownVariableList" = null; --belongs to the ideal.
        polynomialSet#"scalingVariableList" = null;

    -- 2. available after successfull lift (tryLiftAndLLLAndPairPolSet)  . Requires  1.:createLiftInputData()
    polynomialSet#"rootList" = null; --  at the end sub ( ideal,rootlist )< eps ;   
    polynomialSet#"liftInfo" = null;
  
    --3.  available after vanishedSetToRFSSolution()-transformation. Requires  2.: successfull lift
    polynomialSet#"solutionIdeal" = null;
    polynomialSet#"solutionList" = null;

  return new RFSPolynomialSet from polynomialSet;
)

createRFSPolynomialSet( RFSProblem, Thing ) := RFSPolynomialSet => (rfsProblem, prePolTuple)->
(
    print "createRFSPolynomialSet";
    assert(class prePolTuple===List or class prePolTuple===Array);

    --apply(polynomialList,el->assert(class el===RingElement));
    polInfoList := new MutableList from apply( prePolTuple, pol->createPolynomialInfo(pol) );
    polTuple  := new RFSPolynomialTuple from polInfoList;

    return createRFSPolynomialSet(rfsProblem,polTuple);
)

normalizePolynomialSetInPlace=method();
normalizePolynomialSetInPlace (RFSPolynomialSet) :=(polSet)->
(
    normalizePolynomialTupleInPlace(polSet#"polTuple", polSet#"rfsProblem"#"normalizationRules");
)


-- todo: eventuell noch polynome auf paarweise ggt==1 testen. 
isFullNormalized=method();
isFullNormalized (RFSPolynomialSet) :=(polSet)->
(

    if (polSet#"rfsProblem"#"normalizationRules"===null) then
    (
        polTuple := polSet#"polTuple";
        if not hasInfinityRoot(polTuple#0) then 
            return false;
    
        if not  hasZeroRoot(polTuple#1) then 
            return false;
    
        if not hasOneRoot(polTuple#2) then 
            return false;
    
        for pos in 0..2 do 
        (
            if (hasConstantFactors (polTuple#pos)) then 
                return false;
        );
    
        return true;
    )
    else
    (
        polTupleCopy := deepCopy(polSet#"polTuple");
        try (  normalizePolynomialTupleInPlace(polTupleCopy, polSet#"rfsProblem"#"normalizationRules") )            then ( return true; )        else (return false; );
    );
)

removeConstantFactorInPlace(RFSPolynomialSet) :=(polSet)->
(
    removeConstantFactorInPlace(polSet#"polTuple");
)

--RFSPolynomialSet == RFSPolynomialSet := (polSet1,polSet2)->
--(
--    if (#polSet1 != #polSet2) then
--        return false;
--    for pos in 0..#polSet1-1 do
--    (
--        if (polSet1#pos#"pol"!=polSet2#pos#"pol") then
--            return false;
--    );
--    return true;
--)


size (RFSPolynomialSet) := (polSet)->
(
    return (#(polSet#"polTuple"));
)

getScalingFilter = method();

getScalingFilter ( RFSPolynomialSet) :=  (polSet)->
(
    return (polSet#"rfsProblem"#"polSetFilter");
)

-- Skalierung muss nach dem permutieren nicht geprüft werden, denn wenn die Polynome übereinstimmen, ist die Skalierung auch erfüllt!
RFSPolynomialSet == RFSPolynomialSet := (x,y)->
(
    if (size x!= size y) then 
        return false;
    --
   

    srcTuple := deepCopy (x#"polTuple");
    removeConstantFactorInPlace(srcTuple);
    normalizePolynomialSetInPlace(srcTuple);
    assert( (getScalingFilter x)(srcTuple,x#"rfsProblem"#"shapeList")  );
    
--
    dstTuple := deepCopy (y#"polTuple");

    removeConstantFactorInPlace(dstTuple);
    normalizePolynomialTupleInPlace(dstTuple,y#"rfsProblem"#"normalizationRules");
    assert( (getScalingFilter y)(dstTuple,x#"rfsProblem"#"shapeList")  );
    --
       
    for permutedDstTuple in permutations new List from dstTuple do 
    (
        equal := true;
        dstPermutedPolTuple :=   new RFSPolynomialTuple from permutedDstTuple;
        --
        dstPermutedPolTupleCopy := deepCopy dstPermutedPolTuple;
        removeConstantFactorInPlace(dstPermutedPolTupleCopy);
        normalizePolynomialTupleInPlace(dstPermutedPolTupleCopy,y#"rfsProblem"#"normalizationRules");
         for pos in 0..(#srcTuple-1) do 
         (
                if (srcTuple#pos != dstPermutedPolTupleCopy#pos) then 
                     equal = false;
         );
        if (equal) then return true;
    );
    return false;
)
---------------------------------------------------

RFSPolynomialSetList = new Type of List;


new RFSPolynomialSetList from List := (A,setList)->
(
  for el in setList do
     assert (class el === RFSPolynomialSet);
  return setList;
)


internalUnique = method();
internalUnique (List, RFSPolynomialSet) := (polSetList, polSet)->
(
    resList := {polSet};
    for pos in 0..(#polSetList-1) do 
    (
        if (polSetList#pos!=polSet) then 
            resList = append(resList,polSetList#pos);
    );
    return resList;
)


unique (RFSPolynomialSetList) := (polSetList) ->
(
    resultList := new List from polSetList;
    pos := 0;
    while (pos <= #resultList-1) do 
    (
        resultList = internalUnique(resultList,resultList#pos);
        --print resultList;
        pos=pos+1;
    );
    return resultList;
)
   
--------------------------------------------------

--RFSPolynomialSetTable = new Type of MutableHashTable;

--isConsistent
--createRFSPolynomialSetTable():= ()->



 --  Alternatives benutzerdefiniertes Verhlaten: der Benutzer definiert einen neuen Typ und implementiert die Schnittstelle komplett!
-- dies geht in M2 nicht mit Vererbung, naja, ich verstehe es halt nicht ganz warum es mit Vererbung nicht funktioniert...aber probiert es doch selbst aus!
RFSResultManager = new Type of MutableHashTable;

new RFSResultManager := (A)->
(
    rfsManager :=  new MutableHashTable;
    rfsManager#"resultList"= {};

    rfsManager#"addResult" = (polynomialSet)  ->
    (
         --todo : problem processing result in parallel implementation, depending on implementation eventually need a mutex (currently not).
        rfsManager#"resultList" = append(rfsManager#"resultList",polynomialSet);
    );
    rfsManager#"getResults" = ()  ->
    (
        return rfsManager#"resultList"  ;
    );

    rfsManager#"create" = ()  ->
    (
        return new RFSResultManager  ;
    );  
    rfsManager#"mergeResults" = (rfsResultManager)  ->
    (
         assert(rfsResultManager=!=rfsManager);
         rfsManager#"resultList" =  rfsManager#"resultList" | (rfsResultManager#"getResults"()) ;
         return rfsManager;
    );
    return rfsManager;
)

new RFSResultManager from MutableHashTable := (A,mht)->
(
   assert(false);
)

addResult=method();
getResults=method();
create=method();
mergeResults=method();

addResult (RFSResultManager,RFSPolynomialSet) := (resultManager,polSet)->
(
    (resultManager#"addResult")(polSet);
)

getResults (RFSResultManager) := (resultManager)->
(
    return (resultManager#"getResults")();
)

create (RFSResultManager) := (resultManager)->
(
    return (resultManager#"create")();
)


mergeResults (RFSResultManager, RFSResultManager) := (inoutResultManager,inResultManager)->
(
    return (inoutResultManager#"mergeResults")(inResultManager);
)

