-- nore rin installPackage xy to generate documentation., but not exough, somesthing seems to be cached,
--  to get the recent documentation restart M2 and run installPackage again!

-- TODO: what should happen, if the degree of polynomials is too big?
--      do wee need runtime estimation, and if, how it will be done?
-- TODO: tests for irreducibility.
-- todo: type for ShapeList ?  - all shapes in the list should have same degree!
-- 
-- Stichpunkte Grafikkarten-Implementierung: 
--  nur offensichtlic reduzible Polynome rauswerfen (nullstellentest), oder nur Teillisten der irreduziblen Polynome in den Speicher laden (blockweises abarbeiten)
--
-- zusammenhang zwischen # polynomen vom grad d von bestimmter multiplizitätsstruktur/#anzahl aller Polynone,
-- und anzahl bestimmte elemente in der symmetrischen Gruppe Sd zu Anzahl aller Elemente in Sd.
-- 
-- options to call from GAP/SAGEmath:
-- testIrreduciblePolynomials (true/false) , eventually: maxIrreduciblePolynomialDegree.
---- if testIrreduciblePolynomials is false, 

-- MAGMA: see BraidMonodromy action or  Hurwitz

-- globale Variablen entdecken: z.N. apropos "" vor und nach dem Laden oder als Paket definineren
-- TODO: unique funktion für eine liste von RFSPolynomialSet DONE
-- normierung mit verschieben: nur wenn s auf s abgebildet wird!
-- ZwischenErgebnis rfs: Aufrufoptionen, nach charakteristik sortierte PolynomTupel.
-- Frage: die Polynome nicht vielleicht doch als homogen speichern?- gap hat eigentlich Probleme mit multivariaten Polynomen...
-- für nichtnormierbare Polynomtupel nur Statistik ( wenn überhaupt)
-- Format: 0 - polynomNr - Vielfachheit
--         1 - polynomNr - Vielfachheit
--         8 - polynomNr - Viellfachheit
-- Jedem Polynomtupel sollte eine Lösung zugeordet werden können. Die Zwischenlösung (und zwischenideale) interessieren nicht.
----------- für jedes polynom das polynom in welchem die Koeffizienten mit Unbekannten ersetzt wurden
-- dann eine liste von Records, 
-- hast Du schon die Polynome umsortiert so dass die Reihenfolge 8 0 1 ... ist ?
-- sollten für polynome, für die das Faktor-Verhältnis angegeben ist vor dem Test ob das Faktor-verhältnis erfüllt ist, die Polynome umsortiert werden  (8 0 1) ?

-- sonstiges: man kann in einer IDE Bedingungen für ein Breakpoint definieren!

--# Frage: was ändert sich an der SkalierungsRegeln wenn man normalisiert?
--# Frage: wird die gleiche Skalierungsregel erfüllt, wenn man  verschiedene Normalisierungen (verwende verschiedene Faktoren von verschiedenen Polynomen) ausprobiert?

--#TODO Normalize sollte ebenfalls regeln verwenden und isNormalized sollte zusätzlich zum Tupel Normalisierungsregeln als Parameter haben
--TODO RFSearch als objekt bauen, damit die rekursiven Funktionen weniger Parameter haben.
-- TODO: createScalingRelations und scalingFilter überarbeiten: sollte der ScalingFilter die ShapeList enthalten?

---Macaulay2 
 

newPackage(
     "HurwitzMapConstruction",
     Version => "0.9", 
     Date => "05.11.2011",
     Authors => {{
           Name => "Jakob Kroeker", 
           Email => "kroeker@uni-math.gwdg.de", 
           HomePage => "http://www.crcg.de/wiki/User:Kroeker"},{
           Name => "Hans-Christian Graf v. Bothmer", 
           Email => "bothmer@math.uni-hannover.de", 
           HomePage => "http://www.crcg.de/wiki/Bothmer"}    
      },
     Headline => "Rational Function Search with Algebraic Geometry Methods",
     DebuggingMode => true
)


export{    RFSPolynomialInfo,
    createPolynomialInfo,
    RFSPolynomialSet,
    RFSProblem,
    createPolynomialTuple,
    createNormalizationRule, 
    RFSNormRuleSet,
    deepCopy,
    PolynomialConstructOptions,
    createPolynomialConstructOptions,
    computeNormalizationMap,
    removeConstantFactorInPlace,
    normalizePolynomialSetInPlace,
    commonVariable,
    homogenVariable,
    isAShape,
    Shape,
    createRFSRing,
   createRFSProblem,
    createScalingRelations,
    createRFSPolynomialSet,
    createStrictNormalizationRuleSet,
    RFSShapeList,
    reorderShapeList,
    ShapeLog,
    findLogByRuleStructure,
    computeShape,
    polynomialMatchesShape,
    isIrreducible,
    allRationalZeros,

    findFiniteFieldRFSExamples,
    hasInfinityRoot,
    hasZeroRoot,
    hasOneRoot,
    computeAlphaBeta,
    computeAlpha,
    computeAlphaBetaFactors,
    computeAlphaFactors,
    minCharacteristic,
    createLiftInputData,
    RFSPolynomialSetList,
    vanishedSetToRFSSolution,
    getNumCoefficientUnknowns,
    getNumRequiredCoefficientUnknowns,
    sortFactorsByExponent,
   isFullNormalized,
    findABCD21Examples,
    tryLiftAndLLLAndPairPolSet,
    saveFFRFSResultInGAPfile,
    saveRFSLiftResultInGAPfile
    

 -- note: cannot export size,exponents,degree , partition, but this is not necessary , this function work.
}


--tests
export {
    testFind43222Examples
}

needsPackage "padicLift";

--loadPackage( "padicLift",Reload=>true);
--loadPackage( "padicLift");

-- exportsFrom causes alien entries... when using with 'installPackage'.
--exportFrom_padicLift {
--   "ReducedPadicLiftResult",
--    "LiftOptions",
--   "liftPoint",
--    "nextLift",
--    "computeMinPolys",
--    "approxComplexSolutions",
--    "computeSingleMinPoly",
--    "incrementByOne",
--   "checkLiftOptions",
--    "computeRootsWithGP",
----    "example43222SingleVariableLift",
--    "createLiftOptions"
--}





rationalFunctionSearchProtect=()->
(
    protect scalingRelations ;
    protect polSetFilter ;
    protect normalizeByFirstScalar ;
    protect getRestrictingEquations ;
)

rationalFunctionSearchExport = ()->
(
    exportMutable( scalingRelations);
    exportMutable( polSetFilter);
    exportMutable( normalizeByFirstScalar);
    exportMutable( getRestrictingEquations);
);

--rationalFunctionSearchProtect() -- protect the symbols to check package correctness. 
rationalFunctionSearchExport(); -- export the symbols to make the package work 


load "HurwitzMapConstruction/rfsObjects.m2"

load "HurwitzMapConstruction/rfsIO.m2"
-----------------------------------------------

-- computes a multiplicity structure of an  univariate polynomial or of an homogen polynomial in two variables.
-- by using differentiation and GCD or factoring polynomial algorithm from Singular-Factory.
-- parameters:
--  a polynomial  (homogeneous/nonhomogenous)
--  the variable used in univarPoly


computeShape = method( Options=>{"debug"=>false});


computeShape (RingElement) := Shape => opts -> ( univarPoly ) -> 
(
      -- todo: check if variable is in gens ring univarPoly
      polFactor := factor univarPoly;
      tmpList := flatten for fact in polFactor list  (  for num in 0..((degree fact#0)#0)-1 list fact#1  ); 
      shape := new Shape from rsort tmpList;
     return shape;
)


computeShape (RingElement,RingElement) := Shape => opts -> ( univarPoly,  variable ) -> 
(
    return (computeShape(univarPoly));
)

   




-- todo: internalPolynomialMatchesShape can be wrong. consult factor algorithm in Singular to get the idea why factor works and computeShape not. (or stydy the Berlekamp algorithm)
internalPolynomialMatchesShape = method()

-- computing full shape via 'factor' from Singular and check if the shape match is faster 
-- than using 'internalPolynomialMatchesShape' (implements early break), but
-- in a lower language the latter will always be faster 
internalPolynomialMatchesShape (Shape,RingElement,RingElement) := (shape, univarPoly, variable ) -> (
	assert( #(degree univarPoly) == 1); -- otherwise we have a multigraded ring.
	assert( ring univarPoly === ring variable );
	dualMulStructSize := #(shape#"dual");
	gcdF := univarPoly;
	dF := univarPoly;
	pos := 0; -- position in 'shape#"dual"'  array
	--
	-- the while loop is used instead of apply because it is not possible to return from an apply loop
	while (gcdF != 1_(ring variable) and dF != 0_(ring variable)) do (
		prevDegree := degree(variable, gcdF);
		dF = diff( variable, dF );
		gcdF =  gcd( gcdF, dF );
		referenceDegreeDifference := 0;
		if ( pos < dualMulStructSize) then 
			referenceDegreeDifference = (shape#"dual")_pos;
		if  (prevDegree - degree(variable, gcdF) != referenceDegreeDifference)    then 
			return false;
		pos = pos+1;
	);
	-- if (pos >= dualMulStructSize) then the multiplicity structure was fulfilled:
	return (pos >= dualMulStructSize );
)

isHomogenized = method();
isHomogenized (RingElement, Thing):= ( srcPoly, homogenVar )->
(
    assert(homogenVar===null or (parent class homogenVar)===RingElement); -- todo: wieso ist class homogenVar===PolynomialRing und nicht RingElement?
    -- todo: chech if homogenVar is member of gens ring srcPoly
   if ( homogenVar=!=null and homogenize( srcPoly,homogenVar)== srcPoly) then 
    return true
   else return false;
)


 expectedDegreeIsValid := (polDeg, parDestShape)->
  (
    try (
      if ( polDeg===null ) then 
        return true;
        
    if ( ZZ===(class polDeg) and polDeg>=0 ) then 
    (
      return  ( polDeg == degree parDestShape);
    )
    else 
      return false;
    ) then {} else return false;
  );
  
  
--
-- checks if univarPoly has desired multiplicity structure in given variable.
--
-- todo: funktion sollte dreiwertig sein: ja, nein, weiss nicht?
polynomialMatchesShape = method( Options=>{ "hasNoInfinityRoot"  => false,
                                            "strict"=>true,
                                            "expectedDegree"=>null,
                                            "checkPreconditions"=>true,
                                            "homVar"=>null,
                                            "computeFullShape"=>false} );
                                            
polynomialMatchesShape (Shape,RingElement,RingElement) := Boolean => opts -> ( destShape, srcPoly,  variable ) -> 
(
   hasNoInfinityRoot := opts#"hasNoInfinityRoot";
   checkPreconditions:=  opts#"checkPreconditions";
   homVar := opts#"homVar";
  rng := ring srcPoly;
  expectedDegree :=  opts#"expectedDegree"; 
 
  if (checkPreconditions) then 
  (
    --print "checking preconditions..";
    assert( char rng> (max exponents destShape) ); -- otherwise matching shapes will not detected, because 
    assert( #(gens rng)<=2 ); -- be conservative. if a ring with more variables is required, think about it later.
    assert( rng===( ring variable));
    assert( variable=!=homVar );
    assert( #(select( gens rng, (par)->(par==variable)) ) > 0 );
    assert( expectedDegreeIsValid(expectedDegree, destShape) );

    if (homVar=!=null) then 
    (
       assert( #(select( gens rng, (par)->(par==homVar)) ) > 0 );
       assert(homVar =!= variable ) ;
       assert( rng===( ring homVar));
    );
       
    if ( expectedDegree =!=null and  isHomogenized( srcPoly, homVar )) then 
        assert( opts#"expectedDegree" == (degree srcPoly)#0 );
  );
  
  if (opts#"computeFullShape") then 
  (
     --print "computeFullShape";
      computedShape := computeShape(srcPoly,variable);
      return (computedShape#"shape"===destShape#"shape");
  );
  
  
  if ( hasNoInfinityRoot  ) then
  (
    return internalPolynomialMatchesShape(destShape, srcPoly, variable);
  );  

  if (  expectedDegree =!=null   or isHomogenized( srcPoly,homVar )   ) then 
  (
      degreeDifference := null;
      if (expectedDegree=!=null) then 
      (
        degreeDifference = expectedDegree - degree (variable,srcPoly);
      )
      else 
        degreeDifference = (degree srcPoly)#0- degree (variable,srcPoly);
      assert(degreeDifference>=0);
      if ( degreeDifference>0 ) then 
      (
        modifiedDestShape := removeExponent( destShape, degreeDifference ) ;
        if ( modifiedDestShape === destShape or modifiedDestShape===null ) then 
          return false -- modifying shape failed.
        else
        (
          -- print "using modified shape";
          -- print modifiedDestShape;
          return internalPolynomialMatchesShape ( modifiedDestShape, srcPoly,  variable );   
        );
      )
        else return internalPolynomialMatchesShape ( destShape, srcPoly,  variable );
  );
    
   assert( expectedDegree===null and hasNoInfinityRoot==false );
   assert(not  isHomogenized( srcPoly, homVar ));
   
   -- wenn hier angelangt, kann keine sichere Aussage über den Shape gemacht werden. wenn 'strict' gesetzt->Fehler, ansonsten Warnung.
  
  if (not opts#"strict" ) then
  (
         print "warning: result of 'polynomialMatchesShape' may be not correct. To ensure correctness set option 'strict' to 'true'";
         return internalPolynomialMatchesShape ( destShape, srcPoly,  variable );   
  )
  else 
  (
     failedReasonPrefix :=  "Error: cannot compute shape exactly, because ";    
     detectFailReason   := " polynomial has potential infinity root AND is not homogenized. ";
     howtoWorkaroundStr := " \n Please provide the expected degree of the srcPoly  or \n set option 'strict' to 'false' in order to check polynomials shape even in cases where the result may be not correct. ";
     print (failedReasonPrefix | detectFailReason | howtoWorkaroundStr) ;
     assert(false);
  );
  assert(false);
)


 polynomialTupleMatchesShapeList = method();
polynomialTupleMatchesShapeList(RFSPolynomialTuple,RFSShapeList):=(polTuple,shapeList)->
(
    if (#polTuple!=#shapeList) then 
        return false;
    variable := commonVariable ring polTuple;
    homVar := homogenVariable ring polTuple;
    for pos in 0..#polTuple-1 do
        if not polynomialMatchesShape(shapeList#pos, polTuple#pos#"pol",variable,"homVar"=>homVar)   then 
            return false;
    return true;    
)

polynomialSetMatchesShapeList = method();
polynomialSetMatchesShapeList(RFSPolynomialSet,RFSShapeList):=(polSet,shapeList)->
(
    polTuple:=polSet#"polTuple";
    return polynomialTupleMatchesShapeList(polTuple,shapeList);    
)

-- random generation of nonhomogenous polynomials
randomAff = (polDegree,rng) -> (sum apply(polDegree+1,monomDegree->random(monomDegree,rng)));


showProgress = (current, maximal, discretisation)->
(
	if (current % (maximal//discretisation)) ==0 then 
	(
		print "progress: " ;
		print (toString (current*100.0/maximal) | " %" );
	);
)

-----------------------------------------------------------------------------------
--// Problem: how to get all coefficients of a polynomial ( including zeroes?)

univariatePolynomialFromCoefficientList = (coeffList,variable)->
(
    rng := ring variable;
    --// coefficientRing of coeffList and coefficientRing of variable should match. Is no problem at the point of existing class for Polynomial.
    polynomial := 0_rng*variable;
    apply(#coeffList, coeffPos-> polynomial = polynomial + coeffList#coeffPos*(variable^coeffPos));
    return polynomial;
)

-- does not work for graduated polynomials
polynomialHashTableFromPolynomial=(polynomial)->
(
    rng := ring polynomial;
    coeffRng:=coefficientRing rng;
    polynomialHashTable := new MutableHashTable;
    --assert( #(gens rng )==1);
    variable:= commonVariable rng ;
    polynomialHashTable#"variable"=variable;
    polynomialDegree:=(degree polynomial )#0;
    polynomialHashTable#"degree"=polynomialDegree;
    assert( (last coefficients (polynomial,Monomials=>{variable^polynomialDegree}))_0_0 == 1);
    coefficientList := new MutableList from {};
    apply(polynomialDegree, currDeg-> (coefficientList=append( coefficientList, (last coefficients (polynomial,Monomials=>{variable^currDeg}))_0_0 );));
    polynomialHashTable#"coefficientList"=coefficientList;
    constructedPolynomial := univariatePolynomialFromCoefficientList( append(  coefficientList, 1_rng ) , variable);
    assert(constructedPolynomial==polynomial);
    polynomialHashTable#"polynomial"=constructedPolynomial;
    return polynomialHashTable;
)

--wish: internal 'next' function 

nextPolynomial = (polynomialHashTable) ->
(
    variable := polynomialHashTable#"variable";
    rng := ring variable;
    polynomialDegree:=polynomialHashTable#"degree";

    coefficientList := polynomialHashTable#"coefficientList";
    coeffPos:=0;
    --assert(ring coefficientList#coeffPos===rng);
    coefficientList#coeffPos=coefficientList#coeffPos + 1;
    while (coefficientList#coeffPos==0 and coeffPos<polynomialDegree-1 ) do
    (
        coeffPos=coeffPos+1;
        --assert(ring coefficientList#coeffPos=== rng);
        coefficientList#coeffPos=coefficientList#coeffPos + 1;
    );
    polynomialHashTable#"coefficientList" = coefficientList;
    --print (new List from coefficientList);
    polynomialHashTable#"polynomial" = univariatePolynomialFromCoefficientList( append( coefficientList, 1_rng ) ,variable);
    if ( polynomialHashTable#"polynomial" == variable^polynomialDegree) then
        return null;
    return polynomialHashTable;
)


------------------------------------------------------------------------------------------------------------------------------


-- nun koennte man ja zur cond-fkt noch eine weitere hinzunehmen, welche wiederrum irgendwelche Berechnungen durchführt.
-- es wäre praktisch, wenn Macaulay2 coroutines beherrscht.
internalFilteredDegreeNPolynomials= (variable, degN, currDegree,  polynomial, condFkt )->
(
    characteristic:= char ring variable;
    rng := ring variable;
    polynomialList:={};
    if (currDegree<0) then
    (
        localPolynomial:= polynomial + variable^degN;
        if (condFkt(localPolynomial) ) then 
            return {localPolynomial};
    )
    else
    (
        polynomialList = flatten for coeff from 0 to characteristic-1 list
        (
            internalFilteredDegreeNPolynomials(variable, degN, currDegree -1, polynomial + coeff_rng*(variable^currDegree), condFkt ) 
        );
    );
    return polynomialList;
)

-- create a list of all polynomials in given variable of requested degree degN and satisfying condFkt.
filteredDegreeNPolynomials = (variable, degN,  condFkt)->
(
  rng:=ring variable;
  return internalFilteredDegreeNPolynomials(variable, degN, degN-1, 0_rng*variable, condFkt);
)


degreeNPolynomials = (variable, degN)->
(
  return filteredDegreeNPolynomials(variable, degN, trueCondition);
)



--globals: 
-- irreduciblePolynomialsHashTable
-----------------------------------------------------------------------------------------


IrredPolynomialTable = new Type of MutableHashTable;


new IrredPolynomialTable from MutableHashTable := (A,mht)->
(
  assert(mht#?"variable");
  assert(mht#?"ring");
  assert( #(select( gens mht#"ring" , (par)->(par==mht#"variable")) ) > 0 );
  -- print ("cannot create "|toString A|" from "| toString mht); assert (false); 
  return new MutableHashTable from mht;
);

createIrredPolynomialTable = method();
createIrredPolynomialTable ( RingElement) := (relem)->
(
  if ( (class (ring relem) === PolynomialRing) and   ( #(select( gens ring relem , (par)->(par==relem)) ) > 0 ) ) then 
  (
     tmp:= new MutableHashTable from {("variable",relem ), ( "ring", ring relem ) };
     result := new IrredPolynomialTable from tmp;
     return result;
  )
  else
  (
    print ("cannot create IrredPolynomialTable  from "| toString relem); assert (false); 
  );
);

new IrredPolynomialTable from Thing := (A,c)->
(
  print ("cannot create "|toString A|" from "| toString c); assert (false); 
);

new IrredPolynomialTable of Thing from Thing := (A, B, c)->
(
  print ("cannot create "|toString A|" of "|toString B|" from given "| toString c); assert(false); 
);



new IrredPolynomialTable:= (xyz)->
(
  print ("cannot create IrredPolynomialTable " |  toString xyz); assert (false); 
);

getIrreduciblePolynomials=method();
getIrreduciblePolynomials (IrredPolynomialTable, ZZ):= (irrPolTable, polDeg)->
(
  assert( polDeg>=1 );
  isIrreducibleCondFkt := isIrreducible ; -- todo: default option.
  variable := irrPolTable#"variable" ;
  if (not irrPolTable#?polDeg) then
  (
    if (polDeg>1) then 
      irrPolTable#polDeg=  filteredDegreeNPolynomials(variable, polDeg, isIrreducibleCondFkt  )
    else
      irrPolTable#polDeg =  filteredDegreeNPolynomials(variable, 1, trueCondition  );
    --print (irrPolTable#polDeg);
   -- print (#irrPolTable#polDeg);
    print ( #(irrPolTable#polDeg) | " irreducible polynomials of degree "| toString polDeg |" created" ) ;
  );
  irrPolTable#polDeg
)



removeDegreeOneIrreduciblePolynomial=method();
removeDegreeOneIrreduciblePolynomial (IrredPolynomialTable,RingElement)  := (irrPolTable, polynomial)->
(
  assert(irrPolTable#"ring"===ring polynomial);
  assert( degree(irrPolTable#"variable", polynomial)==1 );
  -- todo, das Polynom darf nur die Variable irrPolTable#"variable" enthalten.
  polDegree := (degree polynomial)#0;
  assert(polDegree==1);
  if (not irrPolTable#?polDegree) then 
    getIrreduciblePolynomials(irrPolTable, polDegree);
  irrPolTable#polDegree = delete(polynomial, irrPolTable#polDegree);
)


-- does only copy polynomials of degree 1, because they are the only ones which may be modified later by the rationalFunctionSearch algorithm
specialCopy=method();
specialCopy (IrredPolynomialTable) := (irrPolTable)->
(
  getIrreduciblePolynomials(irrPolTable, 1);
  specialIrrPolTableCopy := copy irrPolTable;
  assert( specialIrrPolTableCopy#?1 );
  specialIrrPolTableCopy#1= copy irrPolTable#1;
  return specialIrrPolTableCopy;   
)






-- todo: polynomialSet#addFactor() - Funktion ?
applyNormalizationRule = ( normalizationRule,   variable,  polynomialSet )->
(
  print "applyNormalizationRule";
  --sleep 2;
  homVariable := homogenVariable (ring variable);
  whichPolynomial := normalizationRule#"whichPolynomial";
  polFactorExponent :=  normalizationRule#"polFactorExponent";
  if ( normalizationRule#"value"===infinity ) then
  (
      --print normalizationRule#"whichPolynomial";
      polynomialSet#( whichPolynomial )#"factors" = polynomialSet#( whichPolynomial )#"factors" * (new Power from { 1_(ring variable) ,polFactorExponent });
  )
  else
  (
    assert( polynomialSet#?( whichPolynomial ) );
    currFactor := variable - normalizationRule#"value";
    polynomialSet#( whichPolynomial )#"factors" = polynomialSet#( whichPolynomial )#"factors" * (new Power from{ currFactor,  polFactorExponent  });
    --print ("homFactor: " | toString homFactor);
    polynomialSet#( whichPolynomial )#"pol" = polynomialSet#( whichPolynomial )#"pol"* ( currFactor^( polFactorExponent ));
  );
    polynomialSet#( whichPolynomial )#"factors" = factor value  polynomialSet#( whichPolynomial )#"factors";
  normalizationRule#"applied" = true;
  return polynomialSet;
)


findMatchingRulePosition = (currRuleList, normalizationRule )->
(
  if (#currRuleList==0) then
    return null;
  --
  for pos in 0..#currRuleList-1 do
  (
     currRule := currRuleList#pos;
      if ( (normalizationRule#"polFactorExponent"===null or normalizationRule#"polFactorExponent" == currRule#"polFactorExponent")
           and 
           (normalizationRule#"whichPolynomial"===null or normalizationRule#"whichPolynomial" == currRule#"whichPolynomial")
           ) then
           return pos;
  );
  return null;
)

-- debug
--globalCount= 0;

--passedCount=0;

sortRulesByDegree = (constructionRules)->
(
  --print constructionRules;
   sortedRules := new MutableHashTable;
    
    for tmpRule in constructionRules do
    (
        -- whichPolynomial:=tmpRule#"whichPolynomial";
        currDeg := tmpRule#"polFactorDegree";
        --
        if ( not sortedRules#?currDeg) then 
          sortedRules#currDeg={tmpRule}
        else  sortedRules#currDeg = sortedRules#currDeg | {tmpRule};
    ); 
    return sortedRules;
)


sortRulesByExponent = (constructionRules)->
(
   sortedRules := new MutableHashTable;
    --print (peek constructionRules);
    for tmpRule in constructionRules do
    (
      assert(class tmpRule=== PolFactorConstructionRule);
        -- whichPolynomial:=tmpRule#"whichPolynomial";
        currExp := tmpRule#"polFactorExponent";
        --
        if ( not sortedRules#?currExp) then 
          sortedRules#currExp={tmpRule}
        else  sortedRules#currExp = sortedRules#currExp | {tmpRule};
    ); 
    return sortedRules;
)


createRuleStructure = (sortedConstructionRules)->
(
  ruleStructure := new MutableHashTable;
  for currKey in rsort keys sortedConstructionRules do
  (
    currRuleList := sortedConstructionRules#currKey;
    for currRule in currRuleList do
    (
      whichPolynomial := currRule#"whichPolynomial";
      if (not ruleStructure#?whichPolynomial) then 
      (
         ruleStructure#whichPolynomial = new List;
      );
      ruleStructure#whichPolynomial = ruleStructure#whichPolynomial | { (currRule#"polFactorExponent", currRule#"polFactorDegree") };
    );    
  );
  return ruleStructure;
)


constructPolynomialsByShapeLastStage = method();
constructPolynomialsByShapeLastStage := ( rfsProblem , infinityNormApplied, constructOptions, rng,  polynomialTuple, resultManager, shapeLog)->
(
        shapeList:=rfsProblem#"shapeList";
       scalingFilter := rfsProblem#"polSetFilter";
       assert(scalingFilter=!=null);

      --globalCount = globalCount+1;
      variable:= commonVariable rng ;
      homogenVar := homogenVariable rng ;
      --
      --print globalCount;
      --assert(infinityNormApplied);
    
      remainingSubsets := subsets(1..char rng -1,#shapeList-2);
      if ( (#shapeList-2)==1 and constructOptions#"setLambdaToOne") then
      (
        --print "warning: Lambda was set to 1";
        remainingSubsets={{1_rng}};
      );
        
      polynomialTupleIsOK := null;
      
      for currSubset in remainingSubsets do
      (
        polynomialTupleIsOK = true;
                                                        
        for currPos in 0..#currSubset-1 do
        (
          polynomialTuple#(currPos+2)#"pol" = -1_rng*( polynomialTuple#0#"pol" +  (currSubset#currPos)_rng* polynomialTuple#1#"pol");
          
          if (shapeLog=!=null) then 
          (
              computedLog :=  shapeLog#"computeLog"(polynomialTuple, variable ) ;
              addShapeLog(shapeLog, #shapeLog-1, computedLog );
          );
          --assert(infinityNormApplied);
          if (not  polynomialMatchesShape( shapeList#(currPos+2), polynomialTuple#(currPos+2)#"pol", variable, "checkPreconditions"=>false,
                                                  "hasNoInfinityRoot" => infinityNormApplied, "homVar" => homogenVar,
                                                  "computeFullShape"=>constructOptions#"computeFullShape",
                                                  "expectedDegree" => degree shapeList#(currPos+2)) ) then
          (
            --print "not ok";
            polynomialTupleIsOK  = false;
            break;
          );
        );
          if (polynomialTupleIsOK) then 
          (
                expectedDegree := degree shapeList#0;
                tmpPolynomialTuple := deepCopy polynomialTuple;
             --debug: 
             -- print " ok";
             --debug: -- sleep 1;        
            --passedCount = passedCount + 1;
            for pos in 0..#tmpPolynomialTuple-1 do 
            (
                tmpPolynomialTuple#pos#"pol" = homogenize  (tmpPolynomialTuple#pos#"pol",homogenVar);
                polDegree := (degree tmpPolynomialTuple#pos#"pol")#0;
                if (polDegree<expectedDegree) then 
                    tmpPolynomialTuple#pos#"pol" = tmpPolynomialTuple#pos#"pol"*homogenVar^(expectedDegree-polDegree);
                tmpPolynomialTuple#pos#"factors"=factor tmpPolynomialTuple#pos#"pol";
                tmpPolynomialTuple#pos#"shape"=shapeList#pos;
            );
            --some consistency check:
            hasOneInfinityRoot:=false;
            for pos in 0..#tmpPolynomialTuple-1 do 
            (
                if (hasInfinityRoot( tmpPolynomialTuple#pos#"pol") ) then
                (
                    assert(not hasOneInfinityRoot);
                    hasOneInfinityRoot=true;
                );
            );
            --todo: nachdem nun das Tuple gefunden wurde, muss die Reihenfolge entsprechend der ursprünglichen ShapeList umgetauscht werden
            -- falls am Anfang die ShapeList umsortiert wurde um Punkte mit weniger Aufwand zu finden.
            --if (scalingFilter=!=null) then
            polynomialTupleIsOK = (scalingFilter)(tmpPolynomialTuple,shapeList);

            --for pos in 2..#tmpPolynomialTuple-1 do 
            --    tmpPolynomialTuple#pos#"factors"=factor tmpPolynomialTuple#pos#"pol";
            if (polynomialTupleIsOK) then 
            (
                tmpPolynomialSet := createRFSPolynomialSet( rfsProblem, tmpPolynomialTuple);
                addResult (resultManager, tmpPolynomialSet );
            );
          );
      );
     return ;
)

-- todo: is shapeList a constructOption ? 
postConstructPolynomialsByShapeThirdStage = (irredTable, parSortedRules, rfsProblem ,  infinityNormApplied, constructOptions, rng, polynomialTuple, resultManager, shapeLog)->
(
  shapeList:=rfsProblem#"shapeList";

  homogenVar := homogenVariable rng ;
  if (#(keys parSortedRules)==0) then
  (
    return constructPolynomialsByShapeLastStage ( rfsProblem ,  infinityNormApplied, constructOptions, rng,  polynomialTuple, resultManager, shapeLog);
  )
  else
  (
    key := (keys parSortedRules)#0;
    partSortedRulesCopy := new MutableHashTable from parSortedRules;
    remove(partSortedRulesCopy,key);
    assert(parSortedRules#?key);
   
    --
    num := #(parSortedRules#key);
    polynomialList := getIrreduciblePolynomials(irredTable, key);
    currRuleList := parSortedRules#key;
    currRule := null;
    for subset in subsets(0..#polynomialList-1,num) do
    (
          for permutation in permutations subset do
          (
                -- entferne in parSortedRules einen Eintrag und bearbeite ihn
                tmpPolynomialTuple := deepCopy polynomialTuple;

                for currPos in 0..#currRuleList-1 do
                (
                  currRule = currRuleList#currPos;
                  currFactor := polynomialList#(permutation#currPos) ;
                
                  tmpPolynomialTuple#( currRule#"whichPolynomial" )#"factors" = tmpPolynomialTuple#(currRule#"whichPolynomial")#"factors" * (new Power from { currFactor, currRule#"polFactorExponent" });
                  --print  (tmpPolynomialTuple#(currRule#"whichPolynomial")#"pol");
                  --print currFactor;
                  tmpPolynomialTuple#( currRule#"whichPolynomial" )#"pol" =  tmpPolynomialTuple#(currRule#"whichPolynomial")#"pol"*   (currFactor^(currRule#"polFactorExponent"));
                );
                postConstructPolynomialsByShapeThirdStage(irredTable, partSortedRulesCopy ,rfsProblem, infinityNormApplied, constructOptions, rng,  tmpPolynomialTuple, resultManager, shapeLog );
                
          );
    );
    return ;
  );
)

constructPolynomialsByShapeThirdStage = (irredTable, parSortedRules, rfsProblem ,  infinityNormApplied, constructOptions, rng, polynomialSet, resultManager, shapeLog)->
(
    print ("constructPolynomialsByShapeThirdStage not available for older M2 releases");
    assert(false);
)

createPreConstructPolynomialsByShapeThirdStageCall =  (subset, polynomialList,currRuleList, irredTable, partSortedRulesCopy, rfsProblem ,  infinityNormApplied, constructOptions, rng, polynomialSet, resultManager, shapeLog)->
(
  shapeList:= rfsProblem#"shapeList";
  homogenVar := homogenVariable rng;
  innerOBJ := new MutableHashTable;
  innerOBJ#"subset" = copy subset;
  innerOBJ#"resultManager" = create resultManager ;
   
  innerOBJ#"fkt"=  ( )->
        (
         currRule := null;
         retval:=null;
         localSubset := innerOBJ#"subset";
         localManager :=   innerOBJ#"resultManager";
          for permutation in permutations localSubset do
          (
                -- entferne in parSortedRules einen Eintrag und bearbeite ihn
                tmpPolynomialSet := deepCopy polynomialSet;

                for currPos in 0..#currRuleList-1 do
                (
                  currRule = currRuleList#currPos;
                  currFactor := polynomialList#(permutation#currPos) ;
                  
                  tmpPolynomialSet#( currRule#"whichPolynomial" )#"factors" = tmpPolynomialSet#(currRule#"whichPolynomial")#"factors" *(new Power from  { currFactor, currRule#"polFactorExponent" });
                  tmpPolynomialSet#( currRule#"whichPolynomial" )#"pol" =  tmpPolynomialSet#(currRule#"whichPolynomial")#"pol"*   (currFactor^(currRule#"polFactorExponent"));
                );
                currRetVal := postConstructPolynomialsByShapeThirdStage(irredTable, partSortedRulesCopy ,rfsProblem, infinityNormApplied, constructOptions, rng,  tmpPolynomialSet, localManager, shapeLog );
                if (currRetVal=!= null) then
                  retval = retval | currRetVal;
          );
          return retval;
        );
     return innerOBJ;
)







-- todo: rename  sortedRules to degreeSortedPolConstructionRules. 
-- todo: type safety
-- todo: an manchen Stellen sind deepCopy unnötig.
processNormalizationRules = (irredTable, normalizationRules,  rng,   sortedRules, polynomialTuple )->
(
    variable := commonVariable rng ;
  
    assert( class polynomialTuple=== RFSPolynomialTuple);
  
    localPolynomialTuple := deepCopy polynomialTuple;
    
  -- apply all possible normalizationRules
  -- update parA or parC according to current normalization rule
  -- remove used polynomial from polynomialList - better: remove last polynomial or even better just remember the currLastPosition.
  -- remove applied rule from 'sortedRules'
  -- (remove processed NormalizationRule )
  --print (peek sortedRules);
  
  if ( sortedRules#?1 ) then
  (
     currRuleList := sortedRules#1;
      for currNormalizationPos in 0..#normalizationRules-1 do
      (
        matchingRulePosition := findMatchingRulePosition(currRuleList, normalizationRules#currNormalizationPos );
        --assert( matchingRulePosition=!=null );-- todo: dieses assert später rausnehmen. 
        if (matchingRulePosition =!= null) then
        (
          currRule := currRuleList#matchingRulePosition;
          currNormalizationRule := normalizationRules#currNormalizationPos;
          modifiedNormalizationRule := createNormalizationRule(currNormalizationRule#"value", "whichPolynomial" => currRule#"whichPolynomial","polFactorExponent" => currRule#"polFactorExponent");
          normalizationRules#currNormalizationPos= modifiedNormalizationRule;
          --currNormalizationRule#"whichPolynomial" = currRule#"whichPolynomial";
          --currNormalizationRule#"polFactorExponent" = currRule#"polFactorExponent";
          localPolynomialTuple = applyNormalizationRule( modifiedNormalizationRule,  variable, localPolynomialTuple );
          currRuleList = drop( currRuleList, {matchingRulePosition, matchingRulePosition} );
          if ( normalizationRules#currNormalizationPos#"value" =!= infinity ) then 
          (
            --polynomialList = delete(variable-normalizationRules#currNormalizationPos#"value", polynomialList);
            -- removeIrreduciblePolynomial nicht mehr global !
            removeDegreeOneIrreduciblePolynomial(irredTable, variable-normalizationRules#currNormalizationPos#"value" );
          );
        );
      );
      sortedRules#1 = currRuleList;
    );
    return localPolynomialTuple;
)




-- rename to constructPolynomialSetsByShape

constructPolynomialsByShapeSecondStage = (irredTable, polFactorConstructionRules, normalizationRuleSet, rfsProblem, constructOptions, rng,  resultManager, shapeLog )->
(
    shapeList:=rfsProblem#"shapeList";

    polynomialTuple := createPolynomialTuple( #shapeList, rng);
    
    assert( class polynomialTuple=== RFSPolynomialTuple);
    
    degreeSortedConstructionRules := copy sortRulesByDegree( polFactorConstructionRules ); -- rules sorted by degree of factors#
    
    exponentSortedRules := sortRulesByExponent (polFactorConstructionRules);
    
    ruleStructure := createRuleStructure( exponentSortedRules );
   
    normalizationRulesCopy := deepCopy normalizationRuleSet;
    
    --print (#degreeSortedConstructionRules#1);
    --sleep 1;
    print polynomialTuple;
    polynomialTuple  = processNormalizationRules( irredTable, normalizationRulesCopy,  rng, degreeSortedConstructionRules,  polynomialTuple);
    assert( class polynomialTuple=== RFSPolynomialTuple);
    infinityNormApplied := normalizationWasApplied (normalizationRulesCopy, infinity);
    --zeroNormApplied := normalizationWasApplied (normalizationRulesCopy, 0_rng);
    --print (#degreeSortedConstructionRules#1);
    --sleep 1;
    
    if (shapeLog=!=null) then 
      shapeLogAddConstructionRules(shapeLog, degreeSortedConstructionRules);
    if (shapeLog=!=null) then 
       shapeLog#(#shapeLog-1)#"ruleStructure" = ruleStructure;      

    rr := null;
    if (constructOptions#"parallelize") then 
       constructPolynomialsByShapeThirdStage (irredTable, degreeSortedConstructionRules, rfsProblem,  infinityNormApplied, constructOptions, rng, polynomialTuple, resultManager, shapeLog)
    else
       postConstructPolynomialsByShapeThirdStage (irredTable, degreeSortedConstructionRules, rfsProblem,  infinityNormApplied, constructOptions, rng, polynomialTuple, resultManager, shapeLog);
    
    --debug: 
    --if (shapeLog=!=null) then print shapeLog#(#shapeLog-1)#"log";
    --print ("#rr = " |#rr);
    return  ;
)



--todo: bei einem SuchObjekt würden parameter irredTable, rfsProblem,constructOptions, rng, resultManager, shapeLog , normalizationRuleSet wegfallen.

constructPolynomialsByShapeFirstStage = (irredTable, polFactorBlueprintList, polFactorConstructionRules  , normalizationRuleSet, rfsProblem, constructOptions, rng, resultManager, shapeLog )->
(
 
  if (#polFactorBlueprintList==0 ) then
    (
      --print (peek constructionRules) ;
      --sleep 1;
       constructPolynomialsByShapeSecondStage (irredTable,  copy polFactorConstructionRules, normalizationRuleSet, rfsProblem, constructOptions, rng,  resultManager, shapeLog );
    )
  else
  (
	nextPolFactorBlueprint :=  polFactorBlueprintList#0;
	localPolFactorBlueprintList := copy polFactorBlueprintList;
    	localPolFactorBlueprintList  = drop(localPolFactorBlueprintList,{0,0});
      polFactorDegree := nextPolFactorBlueprint#"polFactorDegree";
      polFactorExponent := nextPolFactorBlueprint#"polFactorExponent";
      destPolynomial := nextPolFactorBlueprint#"whichPolynomial";
      for partition in partitions( polFactorDegree ) do
      (
          polFactorConstructionRulesCopy := polFactorConstructionRules | createPolFactorConstructionRules(partition, destPolynomial, polFactorExponent);
          --print polFactorConstructionRulesCopy;
          apply (polFactorConstructionRulesCopy, elem->(assert(class elem===PolFactorConstructionRule)));
          constructPolynomialsByShapeFirstStage(irredTable,  copy localPolFactorBlueprintList, copy polFactorConstructionRulesCopy ,normalizationRuleSet, rfsProblem, constructOptions, rng, resultManager, shapeLog );
      )
  );
  return;
)


constructPolynomialsByShape=(rfsProblem, constructOptions, rng,  polFactorBlueprintList, normalizationRuleSet,  irredTable, resultManager, shapeLog )->
(
  print "constructPolynomialsByShape";
  polFactorConstructionRules := {} ;
  constructPolynomialsByShapeFirstStage( irredTable, polFactorBlueprintList, polFactorConstructionRules, normalizationRuleSet, rfsProblem, constructOptions, rng, resultManager, shapeLog );
  return;
)

globalCounter = 0;

allRationalZeros = (polynomial,variable) -> 
(
    characteristic := char ring polynomial;
    select( characteristic, fieldElem -> 0 == sub(polynomial, variable => fieldElem_(ring polynomial)))
)


hasRationalZeros = (polynomial,variable )->
(
	characteristic := char ring polynomial;
	rng:=ring polynomial;
	for fieldElem from 0 to characteristic-1 do
	(
		
		if (sub(polynomial,variable=>fieldElem_rng)==0) then
			return true;
	);
	return false;
)


findRFSExamplesForGivenCharacteristic = (rfsProblem, characteristic, constructOptions)->
(
    parShapeList:= rfsProblem#"shapeList";
    if (minCharacteristic rfsProblem>=characteristic ) then 
    (
        print "Error: characteristic should be greater than maximal exponent in  all shapes";
        return {};
    );


   rng:= createRFSRing(characteristic); 

   variable := commonVariable rng ;
  
  assert( #parShapeList>0 );

  shapeDegree := degree parShapeList#0;
  apply( parShapeList, shape->assert(degree shape == shapeDegree)); 

    

  shapeList := parShapeList;
  if (constructOptions#"reorderShapeList") then 
    shapeList= reorderShapeList(parShapeList);
  

    
  irredPolTable := createIrredPolynomialTable (commonVariable  rng);
    
  polFactorBlueprintList := {};
  
  -- todo here : arrange multiplicityStructureList  to minimize computation effort.
  
  for currPos  in 0..1 do
  (
    polFactorBlueprintList = polFactorBlueprintList | createPolFactorBlueprintList( shapeList#currPos, currPos );
  );
 
  
  --normalizationRuleZero := createNormalizationRule(0_rng, "polFactorExponent"=>null, "whichPolynomial"=>0 );
  --normalizationRuleOne := createNormalizationRule(1_rng, "polFactorExponent"=>null, "whichPolynomial"=>0 );
  --normalizationRuleInfinity := createNormalizationRule( infinity, "polFactorExponent"=>null, "whichPolynomial"=>1 );
    
    normalizationRuleZero := createNormalizationRule(0_rng, "polFactorExponent"=>null, "whichPolynomial"=>null );
    normalizationRuleOne := createNormalizationRule(1_rng, "polFactorExponent"=>null, "whichPolynomial"=>null );
    normalizationRuleInfinity := createNormalizationRule( infinity, "polFactorExponent"=>null, "whichPolynomial"=>null );

   normalizationRuleSet := constructOptions#"normalizationRuleSet";

    if (normalizationRuleSet===null) then
         normalizationRuleSet = new RFSNormRuleSet from  {normalizationRuleInfinity, normalizationRuleZero, normalizationRuleOne} ;

    print "normalizationRuleSet";
    print normalizationRuleSet;

  -- normalizationRuleSet := new RFSNormRuleSet from { normalizationRuleZero, normalizationRuleOne} ;
  -- normalizationRuleSet := new RFSNormRuleSet from { normalizationRuleInfinity, normalizationRuleZero} ;

   --  normalizationRuleSet := new RFSNormRuleSet from {};
  --
   --

   
   shapeLog := new ShapeLog;
   
   shapeLog#"computeLog" = (polynomialSet, variable)->
   (
     currChar := char ring variable;
     rng := ring variable;
     result := {};
      currStructure := computeShape( polynomialSet#2#"pol", variable );
      --print currStructure;
      return  currStructure ;
   );
   

    resultManager := new RFSResultManager;
    
    time constructPolynomialsByShape(rfsProblem, constructOptions, rng,  polFactorBlueprintList, normalizationRuleSet,  irredPolTable, resultManager, shapeLog );
    

    results := getResults resultManager;
    print "results";
    print results;
   return results;
)

filterNormalizableExamples = (rfsExamples)->
(
    normalizableExamples:={};
     for polSet in rfsExamples do 
            (
                removeConstantFactorInPlace(polSet);
                degOneFactors := getDegreeOneFactors(polSet#"polTuple",3);
                print "degOneFactors";
                print degOneFactors;
                sleep 2;
                if ( #degOneFactors==3 ) then 
                (
                    --normalizePolynomialSetInPlace(polSet);
                    --assert(hasZeroRoot(polSet#0#"pol"));
                    --assert(hasInfinityRoot(polSet#1#"pol"));
                    --assert(hasOneRoot(polSet#2#"pol"));
                    normalizableExamples = append(normalizableExamples,polSet);
                );
            );
    return normalizableExamples;
)

normalizeExamplesInPlace= (rfsExamples)->
(
  for polSet in rfsExamples do 
            (
            removeConstantFactorInPlace(polSet);
            normalizePolynomialSetInPlace(polSet);
    );
)

removeConstantFactorForExamplesInPlace= (rfsExamples)->
(
  for polSet in rfsExamples do 
            (
            removeConstantFactorInPlace(polSet);
    );
)

-- todo: rename PolynomialConstructOptions into RFSPolynomialConstructOptions?

findFiniteFieldRFSExamples = method( );
findFiniteFieldRFSExamples (RFSProblem, PolynomialConstructOptions) := (rfsProblem, constructOptions)->
(


   -- 'earlyBreak' has currently no function : will later break as long as 'minExamples' are computed, no matter if all examples in a specific characteristic were tested or not

    if (constructOptions#"reorderShapeList"==true) then 
    (
        error("error: shapeReordering currently incorrect implemented...");
        --throw("error: shapeReordering currently incorrect implemented...");
    );
    -- todo: wenn Umordnung der ShapeListe erlabt, muss sobald PolynomListe komplett zurückpermutiert werden, da sonst eventuell die Skalierung nicht mehr korrekt ist. 
    -- todo: an Normalize (nachdem tupel gefunden) müssen optional Regeln übergeben werden können (z.B. welcher Faktor in welchem Polynom normalisiert werden soll).

    numExamples:=0;
    currChar := constructOptions#"minChar";
    while (not isPrime currChar) do
            currChar=currChar+1;
    RFSExamples := new MutableHashTable;
    print (    stopConditionFulfilled (constructOptions, currChar,numExamples));

    while (not stopConditionFulfilled (constructOptions, currChar,numExamples) ) do
    (
        --print (    stopConditionFulfilled (constructOptions, currChar,numExamples));
        print  ("findRFSExamples: trying characteristic " | currChar);
        preRFSExamples := findRFSExamplesForGivenCharacteristic (rfsProblem, currChar, constructOptions);
        RFSExamples#currChar={};
        print preRFSExamples;
--
        removeConstantFactorForExamplesInPlace(preRFSExamples);
        if (constructOptions#"onlyNormalizableExamples") then   
        (    
            RFSExamples#currChar = filterNormalizableExamples(preRFSExamples );
            normalizeExamplesInPlace(RFSExamples#currChar);
        )
        else 
            RFSExamples#currChar = preRFSExamples;
        numExamples = numExamples+  #RFSExamples#currChar;
        currChar=currChar+1;
        while (not isPrime currChar) do
            currChar=currChar+1;
    );
    return RFSExamples;
)


-- todo: add scalingFilterOption
-- todo: 

findFiniteFieldRFSExamples (RFSProblem) := opts->(rfsProblem)->
(

    constructOptions := createPolynomialConstructOptions( );

    return findFiniteFieldRFSExamples(rfsProblem, constructOptions)
)




-- searches for first (alpha,beta) that satisfies alpha*polA+beta*polB+polC==0. If no solutions, returns (null,null)
computeAlphaBeta=method()
computeAlphaBeta (RingElement,RingElement,RingElement) :=(polA,polB,polC)->
(
    rng:= ring polA;
    charact := char rng;
    for alpha in 1..charact-1 do 
    for beta in 1..charact-1 do 
    if (alpha*polA + beta*polB + polC ==0 ) then 
        return (alpha_rng,beta_rng);
   return (null,null);
)

computeAlpha=method()
computeAlpha (RingElement,RingElement,RingElement) :=(polA,polB,polC)->
(
    assert(hasInfinityRoot(polA));
    rng:= ring polA;
    charact := char rng;
    for alpha in 1..charact-1 do 
    --if ( polA + alpha*polB - polC ==0 ) then
    if ( polB - alpha*polA == polC  ) then  
        return (alpha_rng);
   return null;
)

computeAlphaFactors=method();
computeAlphaFactors (RFSPolynomialTuple) :=(polTuple)->
(
    alphaFactors :={};
    rng:= ring polTuple;
    charact := char rng;
    for pos in 2..#polTuple-1 do
    (
        alpha :=computeAlpha(polTuple#0#"pol", polTuple#1#"pol",polTuple#pos#"pol");
        if (alpha===null ) then 
           return null
        else
            alphaFactors = append( alphaFactors,alpha);
    );
   -- return null;
   return alphaFactors;
)

computeAlphaFactors (RFSPolynomialSet) :=(polSet)->
(
    return computeAlphaFactors(polSet#"polTuple");
)

computeAlphaBetaFactors=method();
computeAlphaBetaFactors (RFSPolynomialTuple) :=(polSet)->
(
    alphaBetaFactors :={};
    rng:= ring polSet;
    charact := char rng;
    for pos in 2..#polSet-1 do
    (
        alphaBeta :=computeAlphaBeta(polSet#0#"pol", polSet#1#"pol",polSet#pos#"pol");
        if (alphaBeta===null ) then 
           return null
        else
            alphaBetaFactors = append( alphaBetaFactors,alphaBeta);
    );
   return alphaBetaFactors;
)

computeAlphaBetaFactors (RFSPolynomialSet) :=(polSet)->
(
    return computeAlphaBetaFactors(polSet#"polTuple");
)


-- todo: ueberlegen, wie man output fuer gap und macaulay bekommt.

-- modifies polynomial set!
-- todo: funk

createExamplePolSet=()->
(
    rng:=createRFSRing(11);
    t:=commonVariable rng;
    s:=homogenVariable rng;
    
    A := (t)^4*(t+3*s)^3*(t^3-3*t*s^2-5*s^3)^2;
    B := (s)^4*(t-5*s)^3*(t^3+3*t^2*s+2*t*s^2+3*s^3)^2;
    C := (t-s)^4*(t-3*s)^3*(t^3-2*t*s^2-3*s^3)^2;

    AInfo := createPolynomialInfo(A);
    BInfo := createPolynomialInfo(B);
    CInfo := createPolynomialInfo(C);

    polSet := new RFSPolynomialSet from {BInfo,AInfo,CInfo};
    -- polSet= new RFSPolynomialSet from {  AInfo,BInfo,CInfo}
    return polSet;
)

testScalingRelations=()->
(
    -- restart
     loadPackage("HurwitzMapConstruction",Reload=>true);
    debug HurwitzMapConstruction;

     loadPackage ("padicLift",Reload=>true);
    debug padicLift;
  
    
    polSet := createExamplePolSet();

    emptyScalingRelations :=createScalingRelations( null,false );

    --assert( true == emptyScalingRelations#"polSetFilter"(polSet) );

    --scalingRelations := createScalingRelations( { {3,1} }, false );
    --scalingRelations := createScalingRelations( { {3,0} }, true );
    scalingRelations := createScalingRelations( { {0,1} }, true );

    --scalingRelations#"polSetFilter"( polSet ); -- ok, ahs to fail!

    multiplicityStructureList := { { 2,1 }, { 2,1 }, { 2,1 }, { 2,1 } };
    --computeRationalFunction( multiplicityStructureList );

    shapeList := new RFSShapeList from apply(multiplicityStructureList, el->new Shape from el);

    rfsProblem := createRFSProblem(shapeList,scalingRelations);

    sortedPolSetList := findFiniteFieldRFSExamples(rfsProblem, 
                                               "onlyNormalizableExamples"=>true );

    fullSortedPolSetList := findFiniteFieldRFSExamples(rfsProblem, 
                                               "onlyNormalizableExamples"=>true,
                                               "minExamples"=>2  );

    polSetList := {};
    for key in keys sortedPolSetList do
        polSetList = polSetList | sortedPolSetList#key;

    polSetList = unique polSetList;

    fullPolSetList := {};
    for key in keys fullSortedPolSetList do
        fullPolSetList = fullPolSetList | fullSortedPolSetList#key;

    fullPolSetList = unique fullPolSetList;

    polSet = polSetList#0;
    -- now, because of the additional scaling condition, the polSet should lift.
    
    removeConstantFactorInPlace( polSet );
    normalizePolynomialSetInPlace( polSet );

    numNormalizedFactorsToExtract := 3;
    
    ( IZ, solutionPoint, equations, scalingVariableList ) := createLiftInputData(polSet, numNormalizedFactorsToExtract, scalingRelations );

    assert(sub(IZ, solutionPoint)==0);

    liftOptions:= new LiftOptions;
 
    liftOptions.maxLatticeDim = 7;
    liftOptions.verbose=true;
    generatorList := gens ring IZ;
    unknownList := generatorList_{0..(#generatorList-3)};
    -- besser: unknownList = generators \ {commonVar,homogenVar}.
    --
    (pollist, rootList, liftInfo) := approxComplexSolutions(IZ, solutionPoint, unknownList, "options"=>liftOptions);

    
)

-- hier kein output file name, sondern für Funktion und Nullstellenberechnen zwei getrennte Methoden mit zwei getrennten Rückgabetypen.

computeRationalFunction = method(Options=>{ (symbol decimalPrecision=>10),
                                          --  (symbol scalingRelationList=>null),
                                           -- (symbol normalizeByFirstScalar=>false)
                                         }  );
computeRationalFunction (List) := opts->(multiplicityStructureList,scalingRelationList,normalizeByFirstScalar)->
(

    shapeList := new RFSShapeList from apply(multiplicityStructureList, el->new Shape from el);

    assert(#scalingRelationList==(#multiplicityStructureList-3));

    normalizationRuleZero := createNormalizationRule(0, "polFactorExponent"=>null, "whichPolynomial"=>null );
    normalizationRuleOne := createNormalizationRule(1, "polFactorExponent"=>null, "whichPolynomial"=>null );
    normalizationRuleInfinity := createNormalizationRule( infinity, "polFactorExponent"=>null, "whichPolynomial"=>null );
  
    normalizationRuleSet := new RFSNormRuleSet from  {normalizationRuleInfinity, normalizationRuleZero, normalizationRuleOne} ;
  
    scalingRelations := createScalingRelations( scalingRelationList, normalizeByFirstScalar );


    rfsProblem := createRFSProblem( shapeList, scalingRelations );

    -- TODO: im Nachhinein NormalizableExamples rausfiltern
    sortedPolSetList := findFiniteFieldRFSExamples(rfsProblem, 
                                               "onlyNormalizableExamples"=>true,
                                               "scalingFilter"=>rfsProblem#"polSetFilter" );
 
  
    
    -- num übergebe scalingFilter   

    polSetList := {};
    for key in keys sortedPolSetList do
        polSetList = polSetList | sortedPolSetList#key;

    polSetList = new RFSPolynomialSetList from polSetList;

    --nachträgliches Filtern: 
    filteredPolSetList:= select(polSetList, (polSet)-> (rfsProblem#"polSetFilter"(polSet)==true) );

    polSetList = unique polSetList;

    apply(polSetList, el -> char el);

    polSet := polSetList#0;

    
    polSet = polSetList#11#0;

    removeConstantFactorInPlace(polSet );
    normalizePolynomialSetInPlace(polSet);

    numNormalizedFactorsToExtract := 3;
    
    ( IZ, solutionPoint, equations, scalingVariableList ) := createLiftInputData(polSet, numNormalizedFactorsToExtract, scalingRelations );

    assert( sub(IZ, solutionPoint) == 0 );

    liftOptions:= new LiftOptions;
    liftOptions.maxLatticeDim = 7;
    liftOptions.verbose=true;
    generatorList := gens ring IZ;
    unknownList := generatorList_{0..(#generatorList-3)};
    -- besser: unknownList = generators \ {commonVar,homogenVar}.
    --
    (pollist, rootList, liftInfo) := approxComplexSolutions(IZ, solutionPoint, unknownList, "options"=>liftOptions);

   

    eps := max flatten apply( apply(rootList,root->sub(gens IZ,root)),el->flatten entries el);
      print eps;

    decimalPrecision=16;
    solutionList := vanishedSetToRFSSolution (polSet, rootList, {unknownList,scalingVariableList}  , decimalPrecision);

)


-- todo: optional break condition on first found example?
-- todo: random search for higher degree polynomials?
-- are duplicates possible if all three normalization rules  (0,1,inf) ere applied? - YES...
-- are duplicates possible if less than three normalization rules were applied?
-- todo: Funktioniert die Normalisierung für (ABCD) genauso wie für (ABC) ?
findABCD21Examples = (minCharacteristic)->
(
 -- load "HurwitzMapConstruction.m2";
 
  multiplicityStructureList := { {2,1}, {2,1}, {2,1}, {2,1} };
  shapeList := new RFSShapeList from apply(multiplicityStructureList, el->new Shape from el);
--
  --
    rfsProblem := createRFSProblem(shapeList);
    RFSExamples := findFiniteFieldRFSExamples( rfsProblem, "minChar"=>minCharacteristic );
    --print RFSExamples;
    return RFSExamples;
)




-- constructIdealFromExample



load "HurwitzMapConstruction/rfsTests.m2"
load "HurwitzMapConstruction/rfsPrepareLift.m2"


--------------------------------------------------- TESTS

TEST ///
testPolynomialMultiplicities();
///

TEST ///
testFilteredDegreeNPolynomials();
///

TEST ///
testPolynomialMatchesShape();
///

TEST ///
testCreateNormalizationRules();
///


TEST ///
testCreateProcessingEntries();
///

 

TEST ///
testCreateSortedRules();
///



TEST ///
--applyNormalizationRule = (normalizationRule, whichPolynomial, polFactorExponent,  parA, parC )
---
///


---
end
---
---
end
---
 


-- parallelToolbox is only in Macaulay2 trunk!
constructPolynomialsByShapeThirdStage = (irredTable, parSortedRules, rfsProblem ,  infinityNormApplied, constructOptions, rng, polynomialTuple, resultManager, shapeLog)->
(
  --print "enter constructPolynomialsByShapeThirdStage";
--
  if (#(keys parSortedRules)==0) then
  (
    return constructPolynomialsByShapeLastStage ( rfsProblem ,  infinityNormApplied, constructOptions, rng,  polynomialTuple, resultManager, shapeLog);
  )
  else
  (
    key := (keys parSortedRules)#0;
    partSortedRulesCopy := new MutableHashTable from parSortedRules;
    remove(partSortedRulesCopy,key);
    assert(parSortedRules#?key);
    --
    num := #(parSortedRules#key);
    polynomialList := getIrreduciblePolynomials(irredTable, key);
    currRuleList := parSortedRules#key;
   --
      ctask:=null;
      taskList:={};
      fkt:=null;
      functionList:={};
    fktEnvelopList:={};
      print polynomialList;
      currRetValNew := null;
    --
      print "cannot be parallelized easily here: gcd uses Singular  and Singular is not threadsafe.\n The safest possibility is to call new M2 processes and grab the result at the end... \n Current implementation: tasks are serialized (proof of concept)";
      --assert(false);
      --sleep 5;
      for subset in subsets(0..#polynomialList-1,num) do
      (        
          localSubset := copy subset;
          fktEnvelop:= createPreConstructPolynomialsByShapeThirdStageCall( subset, polynomialList,currRuleList, irredTable, partSortedRulesCopy, rfsProblem ,  infinityNormApplied, constructOptions, rng, polynomialTuple, resultManager, shapeLog);
          fktEnvelopList = append(fktEnvelopList,fktEnvelop);
        currTask:=createTask(fktEnvelop#"fkt");
          taskList = taskList | {currTask};
          functionList = functionList | {fkt };
      );
      apply(taskList,elem->print elem);
      print "tasks created ";
    -- print (#taskList);
    --
      tasksFinishedFkt := ()->(return true;);
      tasksFinished := createTask(tasksFinishedFkt);
    --  
    -- for ctask in taskList do
    --   addDependencyTask(tasksFinished,ctask);
    --  print "dependency update ";

      for ctask in taskList do ( 
          print ctask;
          if (not isReady(ctask)) then 
            (print "schedule task"; schedule(ctask));  
          print "waiting for task"; 
          -- serialize to check if it works at all
          while (not isReady (ctask)) do {  sleep 1 }; 
          print "task finished";
      );
      --scheduledTaskList := for task in taskList list  schedule(ctask);
      --for ctask in taskList do ( print ctask; if (not isReady(ctask)) then ( schedule(ctask); print ctask ;));
      --
      --schedule(tasksFinished);
      --apply(scheduledTaskList,elem->print elem);
      print "scheduled";
    
      print "waiting finishing";
      --waiting for finishing:
      for ctask in taskList do ( print ctask;  while (not isReady (ctask)) do {  sleep 1 });
      --while (not isReady (tasksFinished) ) do 
      --{sleep 10;   print "not finished"; sleep 10;};
      print "finished";
      finalRetVal := {};
      print ("#fktEnvelopList= " | #fktEnvelopList);
      for fktEnvelop in fktEnvelopList do
      {
           --print ("#fresults= " | #(fktEnvelop#"resultManager"#"getResults"()));
          mergeResults (resultManager, fktEnvelop#"resultManager");
      };
      return  ;  
  );
)


--restart


--load "HurwitzMapConstruction.m2"

ZZ/7[x]
time apply (degreeNPolynomials(x,3), poly->isIrreducible(poly));
time apply (degreeNPolynomials(x,3), poly->isIrreducibleExpensive(poly));




