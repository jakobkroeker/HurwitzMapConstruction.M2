-- calculate p-adic lifts
--
--TODO: write tests, 
-- TODO: introduce LiftInfo, whoch contains latticeDimension and LiftDepth

-- wieder gleiches Problem mit Symbolen: wenn man eine lokale Variable definiert die gleich wie das Symbol heisst, han man Schwierigkeiten mit dem '.' Operator auf den Hastable-Eintrag zuzugreifen



extractAndDropNormalizedRootFactor = method();
extractAndDropNormalizedRootFactor(RFSPolynomialInfo):=(polinfo)->
(
    for pos in 0..#(polinfo#"factors")-1 do
    (
        factVal:=value (polinfo#"factors"#pos);
        normalizedRoot := polinfo#"factors"#pos;
        if ( hasOneRoot(factVal) or hasInfinityRoot(factVal) or hasZeroRoot(factVal)) then 
        (          
            polinfo#"factors"= drop(polinfo#"factors",{pos,pos});
            polinfo#"pol"=  value polinfo#"factors";
            return normalizedRoot;
        );
    );
    return null;
)

-- todo: du machst die selben Fehler die du bei den anderen anmeckerst. 
-- retuns a Hashtable of the normalized factors of the polynomial set and drops them in the polSet . 
-- The Hastable-key is the position in polSet and the value is the normalized factor of type 'Power'
extractAndDropNormalizedFactors = method();
extractAndDropNormalizedFactors (RFSPolynomialTuple,ZZ) := (poltuple,numOfFactorsToExtract)->
(
    normalizedFactors:= new MutableHashTable;
    normalizedFactor:= null;
    oneRootCount:=0;
    zeroRootCount:=0;
    infinityRootCount:=0;
    for pos in 0..#poltuple-1 do
    (
        normalizedFactor=1;
        while (normalizedFactor=!=null) do
        if (numOfFactorsToExtract> #(keys normalizedFactors)) then 
        (
            normalizedFactor = extractAndDropNormalizedRootFactor(poltuple#pos);
            if (normalizedFactor=!=null) then 
            (
                if ( not normalizedFactors#?pos) then 
                     normalizedFactors#pos = {};
                normalizedFactors#pos = normalizedFactors#pos | {  normalizedFactor };
                if (hasOneRoot(value normalizedFactor)) then 
                    oneRootCount=oneRootCount+1;
                if (hasZeroRoot(value normalizedFactor)) then 
                    zeroRootCount=zeroRootCount+1;
                if (hasInfinityRoot(value normalizedFactor)) then 
                    infinityRootCount=infinityRootCount+1;
            );
        )
        else 
            break;

    );
    assert(oneRootCount<=1);
    assert(zeroRootCount<=1);    
    assert(infinityRootCount<=1);
    return normalizedFactors;
)


-- returs a mutableHashTable wit exponents of the factors as keys and a product of factors 
sortFactorsByExponent (Product) := (polFactors)->
(
    result:= new MutableHashTable;
    for fact in polFactors do
    (
        assert(fact#1 >= 1);
        if (not result#?(fact#1)) then  
            result#(fact#1)=new Power from (fact#0,1)
        else
          result#(fact#1)= result#(fact#1)*(new Power from (fact#0,1));
    );
    return result;
)

getRequiredVariablesNum:=(exponentSortedFactors)->
(
    num:=0;
    for key in keys exponentSortedFactors do
        num=num+(degree value exponentSortedFactors#key)#0;
    return num;
)

polSetToPointCoordinates = method();

polSetToPointCoordinates (RFSPolynomialTuple,RFSPolynomialTuple,Boolean):=(reducedPolTuple,polTuple,bNormalizeByFirstScalar)->
(
    assert(#polTuple>=3);
    rng := ring polTuple;
    pointCoordinates :={};
        print "createLiftInputData: computeAlphaFactors";
     alphaFactors     := computeAlphaFactors(polTuple);
    
    assert( alphaFactors=!=null );

    for pos in  0..(#reducedPolTuple-1) do
    (

        polInfo := reducedPolTuple#pos;

        for factorExponent  in rsort keys  polInfo#"byExponentSortedFactors" do   
        (
            currPolynomial := value polInfo#"byExponentSortedFactors"#factorExponent;
            currPolynomialDegree := (degree currPolynomial)#0;
            srcMonomials := apply(currPolynomialDegree+1, exponent->((homogenVariable rng)^exponent*(commonVariable rng)^(currPolynomialDegree-exponent)));
            currCoefficients := last coefficients(currPolynomial,Monomials=>srcMonomials);
            assert(numColumns currCoefficients==1);
            assert(currCoefficients_0_0==1_rng);  -- if this assertion fails, the factor probably contains  infinite root or is not monic.
            for row in 1..(numRows currCoefficients)-1  do
                 pointCoordinates=append(pointCoordinates,currCoefficients_0_row);
        );
    );

    alpha:=null;
     
    alpha = computeAlpha(polTuple#0#"pol",polTuple#1#"pol",polTuple#2#"pol");
    pointCoordinates=  pointCoordinates  | { alpha } ;
       
    for pos in 3..#polTuple-1 do
    (    
       
        scalingFactor := computeAlpha(polTuple#0#"pol",polTuple#1#"pol",polTuple#pos#"pol");
        if (bNormalizeByFirstScalar) then 
            scalingFactor=scalingFactor*alpha^-1;

        pointCoordinates=  pointCoordinates  | { scalingFactor } ;
        
    );
    return pointCoordinates;
)



--polset parameter: polynomial set where the normalized factors are removed (0,1, infinity)
--todo: check this precondition!
getNumCoefficientUnknowns=method();
getNumCoefficientUnknowns(RFSPolynomialTuple) := ZZ=> (modifiedPolTuple)->
(
    numCoeffUnknowns:=0;
    for polInfo in modifiedPolTuple do
        (
            for factorExponent  in rsort keys  polInfo#"byExponentSortedFactors" do   
            numCoeffUnknowns = numCoeffUnknowns+ (degree value polInfo#"byExponentSortedFactors"#factorExponent)#0;
        );
    return numCoeffUnknowns;
)

getNumRequiredCoefficientUnknowns=method();
getNumRequiredCoefficientUnknowns(RFSPolynomialTuple) := ZZ=> (polTuple)->
(
     polTupleCopy := deepCopy polTuple;
    --
    assert(#polTuple>=3);
    rng := ring polTuple;
  --
    normalizedFactorsToExtract := 3;
    
    normalizedRoots:= extractAndDropNormalizedFactors(polTupleCopy, normalizedFactorsToExtract);
      numCoeffUnknowns:=0;
    for polInfo in polTupleCopy do
        (
               sortedFactorsByExponent:= sortFactorsByExponent polInfo;
            for factorExponent  in rsort keys  sortedFactorsByExponent  do   
            numCoeffUnknowns = numCoeffUnknowns+ (degree value sortedFactorsByExponent#factorExponent)#0;
        );
    return numCoeffUnknowns;
)



createIdealTerm=(polInfo, dstRng, unknownVariableList,coeffVarIdx)->
(   
    currPolynomialTerm:= 1_dstRng;
    currFactor:=null;
   for factorExponent  in rsort keys  polInfo#"byExponentSortedFactors" do
   (
        currPolynomial := value polInfo#"byExponentSortedFactors"#factorExponent;
        currPolynomialDegree := (degree currPolynomial)#0;
        assert(currPolynomialDegree>0);
        currFactor = 1_dstRng*(commonVariable dstRng)^(currPolynomialDegree);
        for homVarExponent in 1..currPolynomialDegree do
        (
            currFactor = currFactor + unknownVariableList_coeffVarIdx*(commonVariable dstRng)^(currPolynomialDegree-homVarExponent)*(homogenVariable dstRng)^homVarExponent;
            coeffVarIdx = coeffVarIdx+1;
        );
        currPolynomialTerm = currPolynomialTerm*(currFactor^factorExponent);
   );
    
    polInfo#"idealTerm"=currPolynomialTerm;
    return coeffVarIdx;
)


--# es scheint, dass hier nur zwischen unterschiedlichen Ringen übersetzt wird: der Term normalizedRootFactor wird in  den Ring von dstIdealTerm übersetzt. 
getIdealTermForNormalizedRoot=(dstIdealTerm, normalizedRootFactor)->
(
        srcPolynomial :=normalizedRootFactor#0;
        srcRng:= ring srcPolynomial;
        dstRng:=ring dstIdealTerm;
        currPolynomialDegree := (degree srcPolynomial)#0;
        srcMonomials := apply(currPolynomialDegree+1, exponent->((homogenVariable srcRng)^exponent*(commonVariable srcRng)^(currPolynomialDegree-exponent)));
        dstMonomials := apply(currPolynomialDegree+1, exponent->((homogenVariable dstRng)^exponent*(commonVariable dstRng)^(currPolynomialDegree-exponent)));
        
        currCoefficients := last coefficients(srcPolynomial,Monomials=>srcMonomials);
        currCoefficients = sub( currCoefficients,dstRng );
        dstPolynomial := ((matrix {dstMonomials})*currCoefficients)_0_0;

       dstPolynomial = dstPolynomial^(normalizedRootFactor#1);
        return dstPolynomial; 
)

multiplyIdealTermWithNormalizedRoot=(polynomialInfo,normalizedRootFactor)->
(
       polynomialInfo#"idealTerm"= polynomialInfo#"idealTerm"* getIdealTermForNormalizedRoot( polynomialInfo#"idealTerm", normalizedRootFactor);
        return; 
)


-- todo: um das Problem korrekt hinzuschreiben, muss man den Exponenten des normierten Faktors korrekt ermitteln.
--- todo: doppelter code...
-- voraussetzung: polSet#"ideal" wurde so gebaut, dass die Polynome der Reihe nach abgearbeitet wurden und die Faktoren der einzelnen Polymone vom hächsten zum kleinsten Exponenten, siehe 'createIdealTerm()'!
createSolutionIdeal = method();
createSolutionIdeal( RFSPolynomialSet ) := ( polSet ) ->
(
    assert( isFullNormalized( polSet) );

    assert(polSet#"solutionList"=!=null);
    assert(#(polSet#"solutionList")>0 and #(polSet#"solutionList"#0)>0);

    bitPrecision := -1;
    if   (#(polSet#"solutionList"#0#1)>0) then 
        bitPrecision = precision polSet#"solutionList"#0#1#0#0
    else
        bitPrecision = precision polSet#"solutionList"#0#0#0#0;
    

    scalingRelations:=polSet#"rfsProblem"#"scalingRelationObj";

    polTupleCopy := deepCopy polSet#"polTuple";
    --
    assert(size polSet>=3);
    rng := ring polSet#"polTuple";
    --
    normalizedRoots := extractAndDropNormalizedFactors(polTupleCopy, 3);
    
    numofUnknowns := sum( apply(polSet#"rfsProblem"#"shapeList", shape->size shape)) - 3 ;

     scalingVariableCount :=null;
     
     print "createSolutionIdeal: computeAlphaFactors";
    alphaFactors     := computeAlphaFactors(polSet);
    assert(alphaFactors=!=null);
    
    scalingVariableCount= (size(polSet)-2);
   
    a := null;
    alpha := null;
    t := null;
    s := null;
    unknownVariable:=symbol a;
    scalingVariable:=symbol alpha;
    commonVar := symbol t;
    homVar    := symbol s;

    RFSCCRing:= CC_bitPrecision[  unknownVariable_0..unknownVariable_(numofUnknowns-1),
                     scalingVariable_0..scalingVariable_(scalingVariableCount-1), 
                    commonVar,homVar  ];

       commonVar = (gens RFSCCRing)#(#(gens RFSCCRing)-2);
    homVar = (gens RFSCCRing)#(#(gens RFSCCRing)-1);
    RFSCCRing#"commonVariable" = commonVar;
    RFSCCRing#"homogenVariable" = homVar;

    RFSZZRing:= ZZ[  unknownVariable_0..unknownVariable_(numofUnknowns-1),  
                     scalingVariable_0..scalingVariable_(scalingVariableCount-1), 
                    commonVar,homVar  ];
    commonVar = (gens RFSZZRing)#(#(gens RFSZZRing)-2);
    homVar = (gens RFSZZRing)#(#(gens RFSZZRing)-1);
    RFSZZRing#"commonVariable" = commonVar;
    RFSZZRing#"homogenVariable" = homVar;


    unknownVariableList := (gens RFSZZRing)_{0..(numofUnknowns-1)};
    scalingVariableList := (gens RFSZZRing)_{numofUnknowns..(numofUnknowns+scalingVariableCount-1)};

    print ("unknownVariableList");
    print (unknownVariableList);

    print ("scalingVariableList");
    print (scalingVariableList);

    commonVar = (gens RFSZZRing)#(#(gens RFSZZRing)-2);
    homVar = (gens RFSZZRing)#(#(gens RFSZZRing)-1);

    shapeListCopy := new MutableList from deepCopy  (polSet#"rfsProblem"#"shapeList");

    variablePos := 0;

    for pos  in 0..#(polSet#"polTuple")-1 do
    (
        polInfo := polSet#"polTuple"#pos;

        polInfo#"solutionIdealTerm" = 1_RFSZZRing;
    
        if hasNormalizedRoot(polInfo#"pol") then 
        (
            for normalizedRoot in normalizedRoots#pos do
            (
                polInfo#"solutionIdealTerm" =   polInfo#"solutionIdealTerm"* getIdealTermForNormalizedRoot(  polInfo#"solutionIdealTerm" , normalizedRoot );
                -- remove a shape 
                shapeListCopy#pos = removeExponent( shapeListCopy#pos, normalizedRoot#1);
            )
        );
        shape := shapeListCopy#pos;

        for exp in exponents shape do 
        (
                -- todo : setzt voraus, dass die Faktoren nach grad sortiert sind... man kann ohne diese voraussetzung auskommen!
                polInfo#"solutionIdealTerm" = polInfo#"solutionIdealTerm"*(commonVar-unknownVariableList_variablePos*homVar)^(exp);
            variablePos=variablePos+1;
         
        );
        --print (factor polInfo#"solutionIdealTerm");
    );

    AZ := polSet#"polTuple"#0#"solutionIdealTerm";
    BZ := polSet#"polTuple"#1#"solutionIdealTerm";
--
    equations:={}; 
    currEquation:=null;
    scalingVarIdx:=0;
    CZ:=null;
    for pos in 2..size(polSet)-1 do
    (    
        
        
         CZ := polSet#"polTuple"#pos#"solutionIdealTerm";
        assert(alphaFactors=!=null);
       
        currEquation =  BZ ;

        -- assert(not scalingRelations#"normalizeByFirstScalar");
        ----if ( scalingRelations#"normalizeByFirstScalar" and pos>2) then 
        ----    currEquation = currEquation- (scalingVariableList_0)*(scalingVariableList_scalingVarIdx)*AZ 
        ----else
            currEquation = currEquation- (scalingVariableList_scalingVarIdx)*AZ ;
        scalingVarIdx= scalingVarIdx+1;
        
        currEquation = currEquation - CZ ;
        
        equations = equations | { currEquation };
    );
    polSet#"solutionEquationsDebug" = equations;
    solutionEquations := apply (equations, eqn-> last coefficients(eqn, Variables=>{commonVar,homVar}));
    polSet#"solutionEquations" = solutionEquations;
    polSet#"solutionIdeal" = ideal (solutionEquations);
    polSet#"solutionComplexRing" = RFSCCRing;

)


--precondition: polynomialSet is normalized  
-- todo: sollte fielleicht auch das veränderte polynomialSet zurückgeben. zudem sollte die scalingVariableList zurueckgegeben werden?
-- rueckgabe von equations eigentlich nur fuer debug, braucht sonst niemand.

createLiftInputData = method();
createLiftInputData (RFSPolynomialSet,ZZ) := (polSet, normalizedFactorsToExtract)->
(
    scalingRelations:=polSet#"rfsProblem"#"scalingRelationObj";
    polTupleCopy := deepCopy polSet#"polTuple";
--
    assert(size polSet>=3);
    rng := ring polSet#"polTuple";
  --
    normalizedRoots:= extractAndDropNormalizedFactors(polTupleCopy, normalizedFactorsToExtract);
    --print (peek normalizedRoots);
   -- sleep 10;
--
    variableCount := 0;
--
    for polInfo in polTupleCopy do
    (
        polInfo#"byExponentSortedFactors" = sortFactorsByExponent(polInfo#"factors");
    );
    point := polSetToPointCoordinates(polTupleCopy,polSet#"polTuple",scalingRelations#"normalizeByFirstScalar");
    --print "point";    print point;
--
--
    -- create the ring in ZZ 
        -- find out how many unknowns are required.
  --  
    numofUnknowns := getNumCoefficientUnknowns(polTupleCopy);
    --
    -- find out how many scaling variables are required. (e.g. alpha*A+beta*B+C=0 => scaling variables are alpha and beta.)

    scalingVariableCount :=null;
    print "createLiftInputData: computeAlphaFactors";
    alphaFactors     := computeAlphaFactors(polSet);
   
    assert(alphaFactors=!=null);
    
    scalingVariableCount= (size(polSet)-2);
   
   
    a := null;
    alpha := null;
    t' := null;
    s' := null;
    unknownVariable:=symbol a;
    scalingVariable:=symbol alpha;
    commonVar := symbol t';
    homVar    := symbol s';
--
    RFSZZRing:= ZZ[  unknownVariable_0..unknownVariable_(numofUnknowns-1), 
                     scalingVariable_0..scalingVariable_(scalingVariableCount-1), 
                    commonVar,homVar  ];
--
    -- todo: name 'unknownVariableList' irreführend  - unknowns sind (unknownVariableList + scalingVariableList)...
    unknownVariableList := (gens RFSZZRing)_{0..(numofUnknowns-1)};
    scalingVariableList := (gens RFSZZRing)_{numofUnknowns..(numofUnknowns+scalingVariableCount-1)};
    commonVar = (gens RFSZZRing)#(#(gens RFSZZRing)-2);
    homVar = (gens RFSZZRing)#(#(gens RFSZZRing)-1);
    RFSZZRing#"commonVariable" = commonVar;
    RFSZZRing#"homogenVariable" = homVar;
    --
    -- create the ideal of solutions
    -- transform polSet to pointCoordinates in the ideal of solutions
    --
--
--
    -- create the ideal;
--
    coeffVarIdx := 0;
   --
    for polInfo in polTupleCopy do
    (
        coeffVarIdx = createIdealTerm(polInfo,RFSZZRing,unknownVariableList, coeffVarIdx);
    );
  --
    for pos in 0..1 do
    (
        if (normalizedRoots#?pos) then
        (
            for normalizedRoot in normalizedRoots#pos do
            (
                multiplyIdealTermWithNormalizedRoot( polTupleCopy#pos, normalizedRoot );
            );
        );
        polSet#"polTuple"#pos#"idealTerm"=polTupleCopy#pos#"idealTerm";
    );
--
    AZ:= polTupleCopy#0#"idealTerm";
    BZ:= polTupleCopy#1#"idealTerm";
--
    equations:={}; 
    currEquation:=null;
    scalingVarIdx:=0;
    CZ:=null;
    for pos in 2..size(polSet)-1 do
    (    
        if (normalizedRoots#?pos) then
        (
            for normalizedRoot in normalizedRoots#pos do
            (
                multiplyIdealTermWithNormalizedRoot( polTupleCopy#pos,normalizedRoot );
            )
        );
        
         polSet#"polTuple"#pos#"idealTerm"=polTupleCopy#pos#"idealTerm";

         CZ := polTupleCopy#pos#"idealTerm";
      
        currEquation =  BZ ;

        if ( scalingRelations#"normalizeByFirstScalar" and pos>2) then 
            currEquation = currEquation- (scalingVariableList_0)*scalingVariableList_scalingVarIdx*AZ 
        else
            currEquation = currEquation- scalingVariableList_scalingVarIdx*AZ ;
        scalingVarIdx= scalingVarIdx+1;
        
        currEquation = currEquation - CZ ;
       
        equations = equations | { currEquation };
    );
    
    if (scalingRelations=!=null and scalingRelations#"scalingRelations"=!=null) then 
    (
      
        equations = equations | scalingRelations#"getRestrictingEquations"( scalingVariableList );
    );
    polSet#"equations" = apply (equations, eqn-> last coefficients(eqn, Variables=>{commonVar,homVar}));
    polSet#"ideal" = ideal (polSet#"equations");
    polSet#"point" = matrix {point|{0,0} };
    polSet#"scalingVariableList" = scalingVariableList;
    polSet#"unknownVariableList" = unknownVariableList | scalingVariableList ;

    assert( sub( polSet#"ideal", polSet#"point") == 0 );
    return (polSet#"ideal",  polSet#"point" , equations, polSet#"scalingVariableList" );  
)



-- todo:pari/GP zur Nullstellenberechnung austauschbar machen!

vanishedSetToRFSSolution=method();
vanishedSetToRFSSolution (RFSPolynomialSet, Boolean) := List=> (polSet, includeNormalizedRoots)->
(

    assert(isFullNormalized(polSet));

    assert(polSet#"unknownVariableList"=!=null);
    assert(polSet#"scalingVariableList"=!=null);
 
    unknownList:= polSet#"unknownVariableList";
    scalingList:= polSet#"scalingVariableList";
    assert(#unknownList>0);
    assert(#scalingList>0);  

    assert( polSet#"rootList"=!=null );  
    bitPrecision:= precision polSet#"rootList"#0;
    decimalPrecision := round(log(2)/log(10)*bitPrecision);
    --bitPrecision := round(log(10)/log(2)*decimalPrecision);
  

    srcRing := ring unknownList#0;
    apply(unknownList, unknown->assert(ring unknown===srcRing));
    
    destrng := CC_bitPrecision(gens srcRing);

    destrng#"homogenVariable" = (gens destrng)#(getVariableIdx(srcRing,homogenVariable srcRing) );
    destrng#"commonVariable"  = (gens destrng)#(getVariableIdx(srcRing,commonVariable srcRing) );

    -- rootring required to use pari/gp
    x:=null;
    rootRing := destrng[(symbol x)];

    solutionList:={};

    for root in polSet#"rootList" do
    (
        solution :={};
        for pol in polSet#"polTuple" do 
        (
            partSolution :={};
            sortedFactors := sortFactorsByExponent(pol#"idealTerm");
            for key in rsort keys sortedFactors do
            (
                val:=  sortedFactors#key#0;
                exponent := sortedFactors#key#1;
                if (  hasInfinityRoot(val) and includeNormalizedRoots) then
                (
                    if (includeNormalizedRoots) then
                    (
                        partSolution = partSolution | {(infinity,exponent)}
                    );
                    continue;
                )
                else
                if (not hasNormalizedRoot(val) or includeNormalizedRoots) then
                (
                      val =sub(val, destrng);
                      substituteRules := apply(#unknownList,pos-> (gens ring val)#pos=>root_(0,pos))  | {(homogenVariable ring val)=>1};
                      val = sub(val,substituteRules);
                      val = sub(val, (commonVariable destrng)=>(gens rootRing )#0);
                      factorRootList:= computeRootsWithGP(val, decimalPrecision );
                      partSolution = partSolution | apply(factorRootList, val->(val,exponent));
                );
            );
            solution = solution | {partSolution};
        );

        resultScalingList:={};
         varIdx := getVariableIdx(srcRing,scalingList#0);
        firstScalar := root_(0,varIdx);
        resultScalingList = resultScalingList | {firstScalar};

        for unknown in scalingList_{1..(#scalingList-1)} do 
        (
            varIdx := getVariableIdx(srcRing,unknown);
            scalar:= root_(0,varIdx);
            if ( polSet#"rfsProblem"#"scalingRelationObj"#"normalizeByFirstScalar") then 
                scalar=scalar*firstScalar;
            resultScalingList = resultScalingList | {scalar};
        );
         solution = solution |  {  resultScalingList  };
        solutionList =solutionList | {solution};
    );
    return solutionList;
)

vanishedSetToRFSSolution (RFSPolynomialSet) := List=> (polSet)->
(
    return vanishedSetToRFSSolution(polSet,false);
)

-- remove solutions which are not satisfying scalin
stripNonSolutions = method();
stripNonSolutions(RFSPolynomialSet) :=(polSet)->
(
    newRootList :={};
    firstVarIdx := getVariableIdx(ring polSet#"scalingVariableList"#0, polSet#"scalingVariableList"#0);

    if (polSet#"rfsProblem"#"scalingRelationObj"===null) then
        return;

    scalingRelations := polSet#"rfsProblem"#"scalingRelationObj"#"scalingRelations";

    if (scalingRelations===null or #scalingRelations==0) then 
        return;
    
    --
    for roots in polSet#"rootList" do 
    (
        rootEntries := flatten entries roots;
        --
        passed := true;
        for scalingVarId in 1..#polSet#"scalingVariableList"-1 do
        (
            scalingVariable := polSet#"scalingVariableList"#scalingVarId;
            --
            varIdx := getVariableIdx(ring scalingVariable, scalingVariable);
            --
            computedScalingRelation := rootEntries#varIdx;
            if (not polSet#"rfsProblem"#"scalingRelationObj"#"normalizeByFirstScalar") then
             computedScalingRelation = rootEntries#varIdx/rootEntries#firstVarIdx;
            --
            rp := realPart(computedScalingRelation);
            ip := imaginaryPart(computedScalingRelation);
            --
            if (rp>0 and scalingRelations#(scalingVarId-1)#0<0 or rp>0 and scalingRelations#(scalingVarId-1)#0<0) then
                passed=false;
            if (ip>0 and scalingRelations#(scalingVarId-1)#1<0 or ip>0 and scalingRelations#(scalingVarId-1)#1<0) then
                passed=false;
            --
        );
        if (passed) then 
            newRootList= append(newRootList,roots);
    );
    polSet#"rootList" = newRootList;
)

tryLiftAndLLLAndPairPolSet = method(Options=>{"liftAndLLLOptions"=>new LiftOptions});
tryLiftAndLLLAndPairPolSet (RFSPolynomialSet) := opts->(polSet)->
(
    normalizePolynomialSetInPlace( polSet );

    assert( isFullNormalized( polSet) );
   
    createLiftInputData( polSet, 3 );

    assert( polSet#"ideal"=!=null);
    assert( polSet#"point"=!=null);
    assert( polSet#"unknownVariableList"=!=null);

    (liftAndLLLResult, rootList, liftInfo) := approxComplexSolutions( polSet#"ideal", polSet#"point", polSet#"unknownVariableList",
                                                                   "liftAndLLLOptions"=>opts#"liftAndLLLOptions" );

    
    
    polSet#"rootList" = rootList;
    polSet#"liftInfo" = liftInfo;
    polSet#"minimalPolynomialTable" = liftAndLLLResult;

    -- now get rid of illegal solutions:
    stripNonSolutions(polSet);

    polSet#"solutionList"=  vanishedSetToRFSSolution ( polSet );
    includeNormalizedRoots := true;
    polSet#"fullSolutionList"=  vanishedSetToRFSSolution ( polSet, includeNormalizedRoots );
    
    createSolutionIdeal( polSet );  

    return;
)


-- todo: Funktionen für den RFSZZRing einfuehren.

testCreateIdeal4times21Example=()->
(

    -- load "lift solution.m2";

    characteristic:=7;
    -- multiplicityStructureList := { {2,1}, {2,1}, {2,1}, {2,1} };
    multiplicityStructureList := { {2,2,2,2}, {2,2,2,2}, {7,1} };
    --multiplicityStructureList := { {2,2,2,2,2}, {2,2,2,2,2}, {9,1} };
    --multiplicityStructureList := { {2,2,2}, {2,2,2}, {3,2,1} }; --OK
    --multiplicityStructureList := { {2,2,2}, {2,2,2}, {5,1} };  --no
   -- multiplicityStructureList := { {2,2,2}, {2,2,2}, {4,1,1} }; --no
    --multiplicityStructureList := { {3,2}, {3,2}, {2,2, 1} };
    --multiplicityStructureList := { {2,2, 1}, {3,2}, {3,2}  };

    shapeList := new RFSShapeList from apply(multiplicityStructureList, el->new Shape from el);

     normalizationRuleZero := createNormalizationRule(0, "polFactorExponent"=>null, "whichPolynomial"=>null );
    normalizationRuleOne := createNormalizationRule(1, "polFactorExponent"=>null, "whichPolynomial"=>null );
    normalizationRuleInfinity := createNormalizationRule( infinity, "polFactorExponent"=>null, "whichPolynomial"=>null );
  
    normalizationRuleSet := new RFSNormRuleSet from  {normalizationRuleInfinity, normalizationRuleZero, normalizationRuleOne} ;

    --normalizationRuleSet := new RFSNormRuleSet from  { normalizationRuleZero, normalizationRuleOne } ;

    --normalizationRuleSet := new RFSNormRuleSet from  {};

    polSetList := findFiniteFieldRFSExamples(shapeList,"minChar"=>characteristic, 
                                            "normalizationRuleSet"=>normalizationRuleSet,
                                               "onlyNormalizableExamples"=>false,
                                                "reorderShapeList"=>false  );
 

     -- = findABCD21Examples(characteristic,normalizeFactorCount);
    
    polSet := polSetList#11#0;
    removeConstantFactorInPlace(polSet);
    (IZ,point) := createLiftInputData(polSet,0);

    assert(sub(IZ,point)==0);   
    liftOptions := new LiftOptions;
    --liftOptions#"maxLatticeDim" = 7;
    (pollist, polcomplist) := computeMinPolys(IZ,point,liftOptions);
    
    print toString new Array from pollist;
    print toString new Array from polcomplist;
)



testNormalizeAndLift43222Example=()->
(
    -- load "lift solution.m2";
    Fp := ZZ/11;
    t:=null;
    s:=null;
    t = symbol t;
    s = symbol s;
    R := Fp[t,s];
    
    t= first gens R;
    s=last gens R;
    
    use  R;
    A  :=t^10+2*t^9-5*t^8+3*t^7-4*t^6-5*t^5+t^4;
    Ah := homogenize(A,s)*s^3;

    C :=t^13+2*t^12-5*t^11+5*t^10+t^9-4*t^8-4*t^7-3*t^6-2*t^5+2*t^4+5*t^3+5*t^2+3*t+5;
    Ch := homogenize(C,s);
    Bh := Ah + Ch;

    rng := ring Ah;
    
    rng#"commonVariable"=(gens rng)#0;
    rng#"homogenVariable"=(gens rng)#1;

    
    polSet := new RFSPolynomialSet from {createPolynomialInfo Ah,createPolynomialInfo Ch, createPolynomialInfo Bh};
    normalizePolynomialSetInPlace(polSet);
    (IZ,solutionPoint) := createLiftInputData(polSet,3);

    generatorList := gens ring IZ;
    unknownList := generatorList_{0..(#generatorList-3)};

    assert(sub(IZ,solutionPoint)==0);
    liftOptions := new LiftOptions;
    liftOptions#"maxLatticeDim" = 7;
    (pollist, liftInfo) := computeMinPolys(IZ,solutionPoint,unknownList, liftOptions);
    
    compatibilityUnknownList := apply(#unknownList -1, currvarIdx->( (unknownList)#0 + (unknownList)#(currvarIdx+1)));
    (polcomplist,compatLiftInfo) := computeMinPolys(IZ, solutionPoint, unknownList, liftOptions);
    
    print toString new Array from pollist;
    print toString new Array from polcomplist;
)



example21212121SingleVariableLiftWithoutNormalization=(firstVariableIdx,secondVariableIdx)->
(
    x :=symbol x;
    Xring := ZZ[x];

  
    characteristic:=7;
     multiplicityStructureList := { {2,1}, {2,1}, {2,1}, {2,1} };
    shapeList := new RFSShapeList from apply(multiplicityStructureList, el->new Shape from el);

     normalizationRuleZero := createNormalizationRule(0, "polFactorExponent"=>null, "whichPolynomial"=>null );
    normalizationRuleOne := createNormalizationRule(1, "polFactorExponent"=>null, "whichPolynomial"=>null );
    normalizationRuleInfinity := createNormalizationRule( infinity, "polFactorExponent"=>null, "whichPolynomial"=>null );
  
    --normalizationRuleSet := new RFSNormRuleSet from  {normalizationRuleInfinity, normalizationRuleZero, normalizationRuleOne} ;

    normalizationRuleSet := new RFSNormRuleSet from  { normalizationRuleZero, normalizationRuleOne } ;

    --normalizationRuleSet := new RFSNormRuleSet from  {};

    polSetList := findFiniteFieldRFSExamples(shapeList,"minChar"=>characteristic, 
                                            "normalizationRuleSet"=>normalizationRuleSet,
                                               "onlyNormalizableExamples"=>false );
 

     -- = findABCD21Examples(characteristic,normalizeFactorCount);
    
    polSet := polSetList#11#0;
    removeConstantFactorInPlace(polSet);
    (solutionIdeal,point) := createLiftInputData(polSet,0);
    
    SZ:= ring solutionIdeal;
  
    assert( sub(solutionIdeal, point) == 0 );


    assert ( rank (sub ( jacobian solutionIdeal, point))== numColumns  jacobian solutionIdeal);

    liftOptions:= new LiftOptions;
  
    unknown := (gens SZ)#firstVariableIdx; 
    if (secondVariableIdx=!=null) then 
      unknown = unknown +  (gens SZ)#secondVariableIdx; 
    liftResult := computeSingleMinPoly( solutionIdeal, point, unknown, liftOptions);
  

    fileName:="21212121_withoutNormalization_unknown_";
    if (secondVariableIdx===null) then 
        fileName = fileName | (toString firstVariableIdx) | ".m2"
    else 
        fileName = fileName | "(" | (toString firstVariableIdx)  |","|  (toString secondVariableIdx) | ").m2";


    resultFile:= openOut(fileName);
    
    resultFile << "liftResult:= { (" << firstVariableIdx << "," <<  secondVariableIdx <<")," << (toExternalString (liftResult#"polynomial")) << "};";
    resultFile << close;
)


example21212121SingleVariableLiftWithNormalization=(firstVariableIdx,secondVariableIdx)->
(
    x :=symbol x;
    Xring := ZZ[x];

  
    characteristic:=7;
     multiplicityStructureList := { {2,1}, {2,1}, {2,1}, {2,1} };
    shapeList := new RFSShapeList from apply(multiplicityStructureList, el->new Shape from el);

     normalizationRuleZero := createNormalizationRule(0, "polFactorExponent"=>null, "whichPolynomial"=>null );
    normalizationRuleOne := createNormalizationRule(1, "polFactorExponent"=>null, "whichPolynomial"=>null );
    normalizationRuleInfinity := createNormalizationRule( infinity, "polFactorExponent"=>null, "whichPolynomial"=>null );
  
    normalizationRuleSet := new RFSNormRuleSet from  {normalizationRuleInfinity, normalizationRuleZero, normalizationRuleOne} ;

    --normalizationRuleSet := new RFSNormRuleSet from  { normalizationRuleZero, normalizationRuleOne } ;

    --normalizationRuleSet := new RFSNormRuleSet from  {};

    polSetList := findFiniteFieldRFSExamples(shapeList,"minChar"=>characteristic, 
                                            "normalizationRuleSet"=>normalizationRuleSet,
                                               "onlyNormalizableExamples"=>false );
 

     -- = findABCD21Examples(characteristic,normalizeFactorCount);
    
    polSet := polSetList#7#0;
    removeConstantFactorInPlace(polSet);
    (solutionIdeal,point) := createLiftInputData(polSet,3);
    
    SZ:= ring solutionIdeal;
  
    assert( sub(solutionIdeal, point) == 0 );


    assert ( rank (sub ( jacobian solutionIdeal, point))== numColumns  jacobian solutionIdeal);

    liftOptions:= new LiftOptions;
  
    unknown := (gens SZ)#firstVariableIdx; 
    if (secondVariableIdx=!=null) then 
      unknown = unknown +  (gens SZ)#secondVariableIdx; 
    liftResult := computeSingleMinPoly( solutionIdeal, point, unknown, liftOptions);


    fileName:="21212121_withNormalization_unknown_";
    if (secondVariableIdx===null) then 
        fileName = fileName | (toString firstVariableIdx) | ".m2"
    else 
        fileName = fileName | "(" | (toString firstVariableIdx)  |","|  (toString secondVariableIdx) | ").m2";


    resultFile:= openOut(fileName);
    
    resultFile << "liftResult:= { (" << firstVariableIdx << "," <<  secondVariableIdx <<")," << (toExternalString (liftResult#"polynomial")) << "};";
    resultFile << close;
)



end
------------
-- test sub behaviour

------------
F = sub(random(3,R),{y=>1})
--F = 35*((8/5)*x^3+(3/7)*x^2+10*x+1)
F = 3*(11*x^3+(19/3)*x^2-27*x-4/3) -- Nr 3

factor F

K = ZZ/11
Q =  ZZ[]/11
Rp = K[x,y]
Rpq = Q[x,y]
Fp = sub(F,Rp)
Fpq= sub(F,Rpq)

-------------
--- test LLL----
-------------


R = QQ[x,y]
use R;

F = sub(random(3,R),{y=>1})
--F = 35*((8/5)*x^3+(3/7)*x^2+10*x+1)
F = 3*(11*x^3+(19/3)*x^2-27*x-4/3) -- Nr 3

factor F

K = ZZ/11
Rp = K[x,y]
Fp = sub(F,Rp)
factor Fp;

sub(Fp,{x_Rp=>2})

IF = ideal F
JF = jacobian IF

solution11 = matrix{{1,1_K}} -- die 5-er Nullstelle Funktioniert nicht füer Nr 3, aber die 1-er Nullstelle schon.

sub(solution11,K);

sub(IF,solution11)
liftDepth = 4
liftResultList = liftPoint( IF, solution11, liftDepth );
liftResult=liftResultList#(liftDepth-1)
sub(IF,liftResult)


sub(F,liftResult)




use R

k = 2
M = (sub(sub(matrix{apply(k,i->x^i)},liftResult),ZZ)| sub(matrix{{char ring liftResult}},ZZ));
sM = syz M;

LLL sM^{0..k-1}

k = 3
M = (sub(sub(matrix{apply(k,i->x^i)},liftResult),ZZ)| sub(matrix{{char ring liftResult}},ZZ));
sM = syz M;

LLL sM^{0..k-1}

k = 4
M = (sub(sub(matrix{apply(k,i->x^i)},liftResult),ZZ)| sub(matrix{{char ring liftResult}},ZZ));
sM = syz M;

lres=LLL sM^{0..k-1}

k = 8
M = (sub(sub(matrix{apply(k,i->x^i)},liftResult),ZZ)| sub(matrix{{char ring liftResult}},ZZ));
sM = syz M;

LLL sM^{0..k-1}


coef = sub( last coefficients F,ZZ)
pow = first F
sub(sub(pow,solution11)*coef,Fp)

M = sub(pow,
     liftResult
     )
factor sub((M*sol)_0_0,ZZ)
sub(Fp,solution11)


M
factor F
sub(F,liftResult)

