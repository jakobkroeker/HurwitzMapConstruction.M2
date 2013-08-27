

testNewShape = ()->
(
  newShapeTestPassed := true;
  partitionAsList := {4,3,2,2,2};
  shape:=null;
  a:= symbol a;
  try   (    shape = new Shape from partitionAsList;)  then {} else { assert(false) };   
  
  shape = new Shape from partitionAsList;
  assert (shape#"shape" === new Partition from partitionAsList) ;
  assert (shape#"dual" === conjugate new Partition from partitionAsList) ;
  
  try   (    shape2 := new Shape from shape;  )   then { assert(false) } else {};
    
  try   (    shape = new Shape from null;  )   then { assert(false )} else {};
  
  try   {    shape = new Shape from {3,4};  }    then { assert(false) } else {};
    
  try   {    shape = new Shape from {3,a};  }    then { assert(false) } else {};
    
  try   (    shape = new Shape from (4,3);  )    then { assert(false) } else {};   
  
  try   (    shape = new Shape from new Partition from partitionAsList;)  then {} else { assert(false) };  
  
  print "Test 'testNewShape' passed";
)


testReorderShapeList = ()->
(
    multiplicityStructureList := { {2,2,2,2,2,2,1} , {4,2,2,2,2,1}, {4,3,2,2,2} };
    --
    shapeList := new RFSShapeList from apply(multiplicityStructureList, el->(new Shape from el));
    --
    reorderedShapeList := reorderShapeList(shapeList);
    --
    assert(reorderedShapeList#1===new Shape from {4,3,2,2,2});
    assert(reorderedShapeList#0===new Shape from {4,2,2,2,2,1});
    assert(reorderedShapeList#2===new Shape from {2,2,2,2,2,2,1} );

    multiplicityStructureList = {  {4,4}, {3,2,2,1} , {1,1,1,1,1,1,1,1} };
    --
    shapeList = new RFSShapeList from apply(multiplicityStructureList, el->(new Shape from el));
    --
    reorderedShapeList = reorderShapeList(shapeList);
    assert(reorderedShapeList#0===new Shape from {3,2,2,1});
    assert(reorderedShapeList#1===new Shape from {4,4});
    assert(reorderedShapeList#2===new Shape from {1,1,1,1,1,1,1,1} );

    reorderedShapeList = reorderShapeList(shapeList, "missingDegreeOneFactorPenalty"=>true);
    assert(reorderedShapeList#0===new Shape from {4,4});
    assert(reorderedShapeList#1===new Shape from {3,2,2,1});
    assert(reorderedShapeList#2===new Shape from {1,1,1,1,1,1,1,1} );
)


testGetCoordinatesFromDeg1Factor=()->
(
   characteristic := 7;
    s:=symbol s;
    t:= symbol t;
   rng := ZZ/characteristic[ s,t ];
  commonVariable  := (gens rng)#0;
  homogenVariable := (gens rng)#1;
  s=homogenVariable;
  t=commonVariable;

   rng = new RFSPolynomialRing from rng;
  
  vec1:=getCoordinatesFromDeg1Factor(s,rng);
  assert(vec1_0==1_rng);
  assert(vec1_1==0_rng);
  
  vec1 = getCoordinatesFromDeg1Factor(2*t,rng);
  assert(vec1_0==0_rng);
  assert(vec1_1==2_rng);
  
   vec1 = getCoordinatesFromDeg1Factor(2*s+3*t,rng);
  assert(vec1_0==2_rng);
  assert(vec1_1==3_rng);
)



testConjugateShapePartition = ()->
(
  -- test dual Partition
  assert ( (conjugate partition new Shape from {4,3,2,2,2}) === (partition new Shape from {5,5,2,1}));
  
  print "Test 'testConjugateShapePartition' passed";
)




testNextPolynomial = ()->
(
    x := symbol x;
    rng:= (ZZ/61)[x];
    x = (gens rng)#0;
    polynomialHashTable := polynomialHashTableFromPolynomial(x^3);
    time while (polynomialHashTable=!=null) do
    (
        polynomialHashTable = nextPolynomial( polynomialHashTable );
        --#peek polynomialHashTable;
    );
    -- 40 sec. for deg3 char 61.
)

testIsAShape=()->
(
  a:= symbol a;
  assert(isAShape({4,3,2,2}));
  assert(not isAShape({4,3,2,a}));
  assert(not isAShape({4,3,2,3}) );
   assert(not isAShape({4,3,2,3}) );
   assert(not isAShape(null) );
)



testComputePolynomialShape=()->
(
    s:=symbol s;
    t:= symbol t;
  rng := ZZ/7[ s, t ];

  commonVariable  := (gens rng)#0;
  homogenVariable := (gens rng)#1;
  s=homogenVariable;
  t=commonVariable;
  testPoly:= 0*t;
  
  
  shape := new Shape from {4,3,3};
  testPoly= (s-2*t)^4*(s)^3*(s-1*t)^3; -- unendlich (t^...) kann nicht vorkommen/kommt nicht vor -> infinityNormApplied before.
  computedShape :=  computeShape(testPoly, commonVariable);
  assert( shape ===computedShape);
 
  testPoly= (s-2*t)^4*(t)^3*(s-1*t)^3; -- 0 (s^...) kann nicht vorkommen/kommt nicht vor -> zeroNormApplied before
  print computeShape(testPoly, commonVariable);
  assert( polynomialMatchesShape(shape, testPoly,  commonVariable, "hasNoZeroRoot"=> true, "homVar"=>homogenVariable ));
  testPoly= (s-2*t)^4*(t)^3*(s)^3;
  assert( polynomialMatchesShape( shape, testPoly, commonVariable,  "homVar"=>homogenVariable ));
)

testPolynomialMatchesShape=()->
(
    s:=symbol s;
    t:= symbol t;
  print "** performing Test 'testPolynomialMatchesShape'";
  rng := ZZ/7[ s, t ];
 
  commonVariable  := (gens rng)#0;
  homogenVariable := (gens rng)#1;
  s=homogenVariable;
  t=commonVariable;
  testPoly:= 0*commonVariable;
  
  
  shape := new Shape from {4,3,3};
  testPoly= (s-2*t)^4*(s)^3*(s-1*t)^3; -- unendlich (t^...) kann nicht vorkommen/kommt nicht vor -> infinityNormApplied before.
  --print computeShape(testPoly, commonVariable);
  assert( polynomialMatchesShape( shape, testPoly,  commonVariable,  "homVar"=>homogenVariable ));
  assert( polynomialMatchesShape( shape, testPoly, commonVariable, "hasNoInfinityRoot"=> true,  "homVar"=>homogenVariable ));
  testPoly= (s-2*t)^4*(t)^3*(s-1*t)^3; -- 0 (s^...) kann nicht vorkommen/kommt nicht vor -> zeroNormApplied before
  --print computeShape(testPoly, commonVariable);
  assert( polynomialMatchesShape( shape, testPoly,  commonVariable, "homVar"=>homogenVariable ));
  testPoly= (s-2*t)^4*(t)^3*(s)^3;
  assert(isHomogenized(testPoly,homogenVariable));
  assert( polynomialMatchesShape(shape, testPoly, commonVariable,  "homVar"=>homogenVariable )); -- problem: matching kann nicht ermittelt werden, aber Meldung fehlt...
  assert( polynomialMatchesShape(shape, testPoly, commonVariable,  "homVar"=>homogenVariable,"expectedDegree"=>10 ));
  testPoly= (s-2)^4*(s)^3;
  assert( polynomialMatchesShape(shape, testPoly, commonVariable,  "homVar"=>homogenVariable,"expectedDegree"=>10 ));
  assert( not polynomialMatchesShape(shape, testPoly, commonVariable,  "homVar"=>homogenVariable, "strict"=>false ));
  try (   polynomialMatchesShape(shape, testPoly, commonVariable,  "homVar"=>homogenVariable);  ) then 
     (
      assert(false);  --polynomialMatchesShape should fail with an error
     ) 
  else (  --test passed. 
  );
  print "** Test 'testPolynomialMatchesShape' passed";
)






-- TODO: kann createRules damit umgehen, dass whichPolynomial irgendwelche Zahlen sind und nicht 0,1,2,3 ?
 testCreateProcessingEntries=()->
 (
  whichPolynomial := 23;
  processingEntries := createPolFactorBlueprintList(new Shape from {4,3,2,2,2}, whichPolynomial );
  
  assert( #processingEntries ==3 );
  assert(processingEntries#0#"polFactorDegree" == 1);
  assert(processingEntries#0#"polFactorExponent" == 4);
  assert(processingEntries#0#"whichPolynomial" == whichPolynomial );
  
   assert(processingEntries#2#"polFactorDegree" == 3);
  assert(processingEntries#2#"polFactorExponent" == 2);
  assert(processingEntries#2#"whichPolynomial" == whichPolynomial);
 )
 

testFilteredDegreeNPolynomials=()->
(
    x:=symbol x;
    rng:= (ZZ/61)[x];
    x = (gens rng)#0;
    assert( #filteredDegreeNPolynomials(x,2, trueCondition)==3721);

    rng= (ZZ/7)[x];
    x = (gens rng)#0;
    assert( #filteredDegreeNPolynomials(x,2, trueCondition)==49);
    assert( #filteredDegreeNPolynomials(x,3, trueCondition)==343);

    assert( #filteredDegreeNPolynomials(x,2, isIrreducible )==21);
    assert( #filteredDegreeNPolynomials(x,3, isIrreducible )==112);
)


testCreateSortedRules = ()->
(
    x:=symbol x;
    testrng := ZZ/7[x];
    x = first gens testrng;
  testConstructionRules :=  createPolFactorConstructionRules({1},"A",4);
  testConstructionRules = testConstructionRules | createPolFactorConstructionRules({1},"A",3);
  testConstructionRules = testConstructionRules | createPolFactorConstructionRules({2},"A",2);
  
  testSortedRules := sortRulesByDegree(testConstructionRules);
  assert(testSortedRules#?1==true);
  assert(testSortedRules#?2==true);
  assert(#(testSortedRules#1 ) == 2);
)


testCreateNormalizationRules = ()->
(
  x:=symbol x;
  testrng := ZZ/7[x];
   x = first gens testrng;
  normalizationRuleZero := createNormalizationRule(0_testrng, "polFactorExponent"=>4, "whichPolynomial"=>"A" );
  assert(normalizationRuleZero#"value"==0_testrng);
  assert(normalizationRuleZero#"polFactorExponent"==4);
  assert(normalizationRuleZero#"whichPolynomial"=="A");

  normalizationRuleInfinity := createNormalizationRule(infinity, "polFactorExponent"=>3, "whichPolynomial"=>"A" );
    assert(normalizationRuleInfinity#"value"==infinity);
    assert(normalizationRuleInfinity#"polFactorExponent"==3);
    assert(normalizationRuleInfinity#"whichPolynomial"=="A");
  
)

testProcessNormalizationRules=()->
(
    x:=symbol x;
  testrng := ZZ/7[x];
   x = first gens testrng;
)


testCreatePolFactorConstructionRules=()->
(
  x:=symbol x;
  testrng := ZZ/7[x];
   x = first gens testrng;
  variable := last gens testrng;
  testConstructionRules :=  createPolFactorConstructionRules({1},"A",4);
  testConstructionRules = testConstructionRules | createPolFactorConstructionRules({1},"A",3);
  testConstructionRules = testConstructionRules | createPolFactorConstructionRules({2},"A",2);
)



-- todo: das Gleiche für nicht homogene Polynome ?
-- todo: reicht es, wenn nur zwei Polynome normiert werden können?
testComputeNormalizationMap=()->
(
  Fp := ZZ/11;
  s:= symbol s;
  t:= symbol t;
  R := Fp[s,t];


  R#"commonVariable"  = (gens R)#0;
  R#"homogenVariable" = (gens R)#1;
  t=  R#"commonVariable";
  s=  R#"homogenVariable";

  homVar:= (homogenVariable R);

  use R;
  A:=t^10+2*t^9-5*t^8+3*t^7-4*t^6-5*t^5+t^4;
  Ah := homogenize(A,homVar)*homVar^3;
  C:=t^13+2*t^12-5*t^11+5*t^10+t^9-4*t^8-4*t^7-3*t^6-2*t^5+2*t^4+5*t^3+5*t^2+3*t+5;
  Ch := homogenize(C,homVar);
  B:=A+C;
  Bh:=  homogenize(B,homVar);
  
  assert(computeShape(Ah,(commonVariable R))=== new Shape from {4,3,2,2,2});
  assert(computeShape(Ch,(commonVariable R))=== new Shape from {4,3,2,2,2});
  assert(computeShape(Bh,(commonVariable R))=== new Shape from {4,3,2,2,2});
  
  preAPolInfo := new MutableHashTable;
  preCPolInfo := new MutableHashTable;
  preBPolInfo := new MutableHashTable;
  preAPolInfo#"pol"=Ah;
  preBPolInfo#"pol"=Bh;
  preCPolInfo#"pol"=Ch;
  preAPolInfo#"factors"=factor Ah;
  preBPolInfo#"factors"=factor Bh;
  preCPolInfo#"factors"=factor Ch;
  
  APolInfo :=new RFSPolynomialInfo from preAPolInfo;
  BPolInfo :=new RFSPolynomialInfo from preBPolInfo;
  CPolInfo :=new RFSPolynomialInfo from preCPolInfo;
  
  polSet := new RFSPolynomialSet from {APolInfo,CPolInfo,BPolInfo};
  
  degOneFactors := getDegreeOneFactors(polSet,3);
  assert(#degOneFactors==3);
  for subsetCount in 1..3 do
  {
    for subset in subsets (degOneFactors, subsetCount) do 
    {
    --print "subset";
      --print subset;
      for permutation in permutations subset do 
      {
        -- print "degOneFactors";
        -- print permutation;
        nmap := computeNormalizationMap(permutation);
        mappedAh:=nmap Ah;
        mappedBh:=nmap Bh;
        mappedCh:=nmap Ch;
        assert(mappedBh==mappedAh+mappedCh);
        assert(computeShape(mappedAh,(commonVariable R))=== new Shape from {4,3,2,2,2});
        assert(computeShape(mappedCh,(commonVariable R))=== new Shape from {4,3,2,2,2});
        assert(computeShape(mappedBh,(commonVariable R))=== new Shape from {4,3,2,2,2});
      };
    };
  };
)

--options: setLambdaToOne
-- doHomogenize
-- computeFullShape


-- todo: break condition on first found example?
testFind43222Examples = method();
testFind43222Examples (ZZ,Boolean, Boolean,Boolean) := (characteristic,  computeShapeLog, computeFullShape, parallelize)->
(
 -- 
 -- load "generalizedRationalFunctionSearch.m2";
 
  -- print "allowableThreads";
  -- print allowableThreads;
  -- allowableThreads=3;
  -- print "allowableThreads";
  -- print allowableThreads;
   
  multiplicityStructureList := { {4,3,2,2,2}, {4,3,2,2,2}, {4,3,2,2,2} };
 
  
   assert( #multiplicityStructureList > 0 );
  shapeList := apply(multiplicityStructureList, el->(new Shape from el));
  
  shapeDegree := degree shapeList#0;
  apply( shapeList, shape->assert(degree shape == shapeDegree)); 
  
  -- check if characteristic is big enough
  assert( max apply(shapeList,shape-> max exponents shape) < characteristic ) ;
  
  s:= symbol s;
  t:= symbol t;
  rng := ZZ/characteristic[ s,t ];
  rng#"commonVariable"=first gens rng;
  rng#"homogenVariable"=last gens rng;
  s=first gens rng;
  t=last gens rng;
  -- todo: check  rng#"commonVariable"=!=rng#"homogenVariable".

  irredPolTable := createIrredPolynomialTable ( commonVariable   rng );
  
    
  polFactorBlueprintList := {};
  
  -- todo here : arrange multiplicityStructureList  to minimize computation effort.
  
  
  for currPos  in 0..1 do
  (
    polFactorBlueprintList = polFactorBlueprintList | createPolFactorBlueprintList( shapeList#currPos, currPos );
  );

  
  normalizationRuleZero := createNormalizationRule(0_rng, "polFactorExponent"=>4, "whichPolynomial"=>0 );
  normalizationRuleOne := createNormalizationRule(1_rng, "polFactorExponent"=>4, "whichPolynomial"=>1 );
  
  normalizationRuleTwo := createNormalizationRule(2_rng, "polFactorExponent"=>3, "whichPolynomial"=>0 );
  normalizationRuleInfinity := createNormalizationRule(infinity, "polFactorExponent"=>3, "whichPolynomial"=>0 );
  
   normalizationRules := new MutableHashTable;

   -- infinity rule should be applied first!
   normalizationRuleSet := new RFSNormRuleSet from { normalizationRuleInfinity,normalizationRuleZero,  normalizationRuleOne};

    
  --
  resultFilter := (polynomialSet)->
  (
    assert( polynomialSet#?0 and polynomialSet#?1);
    rng := ring polynomialSet#0#"pol";
    variable := commonVariable  rng ;
    --
    return polynomialMatchesShape( new Shape from {4,3,2,2,2}, polynomialSet#0#"pol" + polynomialSet#1#"pol", variable, "hasNoInfinityRoot" => true);
   );
   --
   --
   shapeLog := new ShapeLog;
   
   shapeLog#"computeLog" = (polynomialSet, variable)->
   (
     currChar := char ring variable;
     rng := ring variable;
     result := {};
      currStructure := computeShape( polynomialSet#0#"pol" + polynomialSet#1#"pol", commonVariable  rng );
      --print currStructure;
      return  currStructure ;
   );
    
    constructOptions := new PolynomialConstructOptions;
    
    constructOptions#"setLambdaToOne"= true;
    constructOptions#"computeFullShape"= computeFullShape; 
    constructOptions#"parallelize"= parallelize;
    
    if (not computeShapeLog) then shapeLog=null;

   resultManager := new RFSResultManager;
    
    time results := constructPolynomialsByShape(shapeList, constructOptions, rng,  polFactorBlueprintList, normalizationRuleSet,  irredPolTable, resultManager, shapeLog );

    print ("#(getResults resultManager) ");
    print (#(getResults resultManager) );
   
    print "finished";
    
    destRuleStructure33 := new MutableHashTable from {0 => {(4, 1), (3, 1), (2, 3)},  
                                                     1 => {(4, 1), (3, 1), (2, 3) }};
                                                   
    
    currLog := findLogByRuleStructure(shapeLog, destRuleStructure33 );
    assert (currLog=!=null);
    
   referenceMultStructureLog := new Tally from {
    {1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1} => 55958,
    {7, 1, 1, 1, 1, 1, 1} => 1,
    {2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1} => 4752,
    {2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1} => 525,
    {2, 2, 2, 1, 1, 1, 1, 1, 1, 1} => 77,
    {2, 2, 2, 2, 1, 1, 1, 1, 1} => 2,
    {2, 2, 2, 2, 2, 1, 1, 1} => 2,
    {3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1} => 654,
    {3, 2, 1, 1, 1, 1, 1, 1, 1, 1} => 43,
    {3, 2, 2, 1, 1, 1, 1, 1, 1} => 9,
    {3, 2, 2, 2, 1, 1, 1, 1} => 1,
    {3, 3, 1, 1, 1, 1, 1, 1, 1} => 10,
    {3, 3, 2, 1, 1, 1, 1, 1} => 1,
    {3, 3, 3, 1, 1, 1, 1} => 3,
    {4, 1, 1, 1, 1, 1, 1, 1, 1, 1} => 106,
    {4, 2, 1, 1, 1, 1, 1, 1, 1} => 3,
    {4, 2, 2, 2, 1, 1, 1} => 1,
    {5, 1, 1, 1, 1, 1, 1, 1, 1} => 10,
    {5, 2, 1, 1, 1, 1, 1, 1} => 2,
    --null => 560 
    };
    --print currLog#"log";
    assert (currLog#"log" === referenceMultStructureLog);
    
    
      destRuleStructure321 := new MutableHashTable from {0 => {(4, 1), (3, 1), (2, 3)},  
                                                        1 => {(4, 1), (3, 1), (2, 2),  (2, 1) }};
                                                   
    
    currLog = findLogByRuleStructure(shapeLog,destRuleStructure321);
    assert (currLog=!=null);
    
     referenceMultStructureLog = new  Tally from {
           {1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1} => 43367,
            {2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1} => 2741,
            {2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1} => 346,
            {2, 2, 2, 1, 1, 1, 1, 1, 1, 1} => 75,
            {2, 2, 2, 2, 1, 1, 1, 1, 1} => 9,
            {2, 2, 2, 2, 2, 1, 1, 1} => 2,
            {3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1} => 397,
            {3, 2, 1, 1, 1, 1, 1, 1, 1, 1} => 11,
            {3, 2, 2, 1, 1, 1, 1, 1, 1} => 3,
            {3, 3, 1, 1, 1, 1, 1, 1, 1} => 7,
            {4, 1, 1, 1, 1, 1, 1, 1, 1, 1} => 63,
            {4, 2, 1, 1, 1, 1, 1, 1, 1} => 1,
            {5, 1, 1, 1, 1, 1, 1, 1, 1} => 18
  --            null => 560
 };
     assert (currLog#"log" === referenceMultStructureLog);
     
     
      destRuleStructure2121 := new MutableHashTable from {0 => {(4, 1), (3, 1), (2, 2),  (2, 1)},  
                                                         1 => {(4, 1), (3, 1), (2, 2),  (2, 1) }};
                                                         
      currLog = findLogByRuleStructure( shapeLog, destRuleStructure2121 );
        assert (currLog=!=null);
                                                   
     referenceMultStructureLog = new  Tally from {
              {1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1} => 23826,
            {2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1} => 999,
            {2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1} => 170,
            {2, 2, 2, 1, 1, 1, 1, 1, 1, 1} => 24,
            {2, 2, 2, 2, 1, 1, 1, 1, 1} => 6,
            {2, 2, 2, 2, 2, 1, 1, 1} => 2,
            {3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1} => 142,
            {3, 2, 1, 1, 1, 1, 1, 1, 1, 1} => 3,
            {3, 3, 1, 1, 1, 1, 1, 1, 1} => 1,
            {4, 1, 1, 1, 1, 1, 1, 1, 1, 1} => 25,
            {6, 1, 1, 1, 1, 1, 1, 1} => 2,
        --            null => 2105
        };
        assert (currLog#"log" === referenceMultStructureLog);
        
        
           destRuleStructure3111 := new MutableHashTable from {0 => {(4, 1), (3, 1), (2, 3)},  
                                                   1 => {(4, 1), (3, 1), (2, 1),  (2, 1),  (2, 1) }}; 
                                                   
          currLog = findLogByRuleStructure( shapeLog, destRuleStructure3111 );
        assert (currLog=!=null);                                           
                
        referenceMultStructureLog = new  Tally from {
            {1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1} => 12996,
            {2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1} => 264,
            {2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1} => 120,
            {2, 2, 2, 1, 1, 1, 1, 1, 1, 1} => 6,
            {3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1} => 42,
            {4, 1, 1, 1, 1, 1, 1, 1, 1, 1} => 12,
--            null => 56560
      };
      assert (currLog#"log" === referenceMultStructureLog);
)


testFindABCD21Examples=()->
(
    assert(#findABCD21Examples(7)==1);
)