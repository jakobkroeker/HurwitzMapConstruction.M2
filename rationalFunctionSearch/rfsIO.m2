
   

--# todo: wenn reorderShape auf False steht, muss mann dann beim Vergleichen von PolynomTupeln bzw beim Normalisieren von Tupeln aufpassen?

--# bug in Macaulay: wenn zwei Variablen in einem Ring gleich heissen, dann scheitert toExternalString

--#-- weitere Probleme: variablen heissen wie schluesselwoerter

convertValueToGap = method();
convertValueToGap := (value)->
(
    if (value===null) then 
        return "[]";
    return value;
)

writeRFScalingRelationsInGAP = method();
writeRFScalingRelationsInGAP(ScalingRelations):=(scalingRelObj)->
(
 if (scalingRelObj#"scalingRelations"===null) then 
        return "[]";
    for entry in scalingRelObj#"scalingRelations" do
         assert(class entry#0===ZZ and class entry#0===ZZ);-- currently only ZZ real and imaginary parts are handled correctly... 
    scalingRelArray := new Array from for entry in scalingRelObj#"scalingRelations" list
         new Array from  entry;
    return toString scalingRelArray;
)

writeRFShapeListInGAP = method();
writeRFShapeListInGAP (RFSShapeList) := (shapeList)->
(
    resultStr:="";
    --
    shapeArray:= new Array from for entry in shapeList list
         new Array from exponents entry;
    --
    return toString shapeArray;
)

writeRFSNormalizationRulesInGAP = method();
writeRFSNormalizationRulesInGAP (RFSNormRuleSet) := (normalizationRules)->
(
    resultStr:="";
    --
    normalizedFactorDegrees:= new Array from for entry in normalizationRules list
         entry#"polFactorExponent";
    --
    return toString normalizedFactorDegrees;
)

writeRFSProblemInGAP=method();
writeRFSProblemInGAP (RFSProblem) := (rfsProblem)->
(
     resultString :=  " rec(";
     resultString = resultString | " shapeList := " | writeRFShapeListInGAP(rfsProblem#"shapeList");
     resultString = resultString | ", scalingRelationList:=" | writeRFScalingRelationsInGAP(rfsProblem#"scalingRelationObj");
     if ( rfsProblem#"normalizationRules"=!=null) then 
    (
       resultString = resultString | ", normalizedFactorDegrees :=" | writeRFSNormalizationRulesInGAP(rfsProblem#"normalizationRules");
    );  
    resultString = resultString | ")";
    return resultString;
)


--## keyList:=["rfsProblem", "polynomialRing", "degree", "polynomialList" ];
-- only for Polynomial ring over ZZ/p, p prime.
writePolynomialRingInGAP= method();
writePolynomialRingInGAP (PolynomialRing) := (polRing)->
(
    characteristic:= char polRing;
    assert( isQuotientOf(ZZ,coefficientRing polRing));
    assert(isPrime(characteristic));
    assert(isPrime((coefficientRing polRing).order));
    --
    resultStr := "PolynomialRing(  Field( Z(" | toString characteristic | ")) ,[" ;
    first:=true;
    for gen in gens polRing do
    (
        if not first then 
              resultStr = resultStr| "," ;
        resultStr = resultStr| "\"" |toString gen |"\"";
       first =false;
    );
    resultStr = resultStr |"] : new )";  
    return resultStr;
)

writeNicePolynomialRingInGAP= method();
writeNicePolynomialRingInGAP (PolynomialRing) := (polRing)->
(
    characteristic:= char polRing;
    assert( isQuotientOf(ZZ,coefficientRing polRing));
    assert(isPrime(characteristic));
    assert(isPrime((coefficientRing polRing).order));
    --
    resultStr := "PolynomialRing(  Rationals  ,[" ;
    first:=true;
    for gen in gens polRing do
    (
        if not first then 
              resultStr = resultStr| "," ;
        resultStr = resultStr| "\"" |toString gen |"\"";
       first =false;
    );
    resultStr = resultStr |"] : new )";  
    return resultStr;
)

writePolynomialTupleInGAP= method();
writePolynomialTupleInGAP (RFSPolynomialTuple) := (polTuple)->
(
    polTupleList:= for pol in polTuple list 
        pol#"pol";
    --
    polArray:=new Array from polTupleList;
    return toExternalString polArray;
)
-- # todo: Problem, wenn Ringvariablen gleiche namen haben...
-- # weiteres potenzielles Problem: überschneidungen von Variablennamen in PolynomialSet.

writeWrappedRFSPolynomialSetInGAP = method( );
writeWrappedRFSPolynomialSetInGAP (RFSPolynomialSet) := (polSet)->
(
    polRing:= ring polSet#"polTuple";
    rngGens:=gens polRing;
    --
    for pos in 0..#(rngGens)-1 do
        (
            assert((toString rngGens#pos) != "ind" );
            assert((toString rngGens#pos) != "polynomialRing" );
            for pos2 in 0..#(rngGens)-1 do
                if (pos!=pos2) then 
                    assert( (toString rngGens#pos)!=(toString rngGens#pos2));
        );
      --
      resultString :="getWrappedRFSPolynomialSet:=function() \n";
      resultString =  resultString | "local polRing,polSet,ind"; 
        --
        for pos in 0..#(rngGens)-1 do
        (
            resultString =  resultString | "," | toString ((gens polRing)#pos) ;
        );
        resultString =  resultString | "; \n ";
       --
        resultString =  resultString | "polRing:= " | writePolynomialRingInGAP(polRing) |";\n";
        resultString =  resultString | " ind:=IndeterminatesOfPolynomialRing(polRing);\n";
        for pos in 0..#(rngGens)-1 do
        (
              resultString =  resultString | toString (rngGens)#pos  | ":=ind[" | toString (pos+1) | "];\n";
        );
      --
      resultString =  resultString | "polSet:= rec(";
      resultString =  resultString | "rfsProblem := " | writeRFSProblemInGAP(polSet#"rfsProblem") | "," ;
      resultString =  resultString | "polynomialRing:= polRing,"; --| writePolynomialRingInGAP(ring polSet#"polTuple") |",";
      resultString =  resultString | "polynomialTuple:= " | writePolynomialTupleInGAP(polSet#"polTuple") |"" ;
      -- todo: idealTerms,
      -- todo: ideal
      -- todo: idealRing
      resultString = resultString |  "); \n";
    resultString =  resultString | "return polSet; \n end;";
    resultString =  resultString | "getWrappedRFSPolynomialSet();";
    return resultString;
)


writeRFSPolynomialSetInGAP = method(Options=>{"defineRing"=>true,"defineProblem"=>true});
writeRFSPolynomialSetInGAP (RFSPolynomialSet) := opts->(polSet)->
(
      resultString :="";
 
     
      resultString =  resultString | " rec(";
      resultString =  resultString | "rfsProblem := " | writeRFSProblemInGAP(polSet#"rfsProblem") | "," ;
      resultString =  resultString | "polynomialRing:= " | writePolynomialRingInGAP(ring polSet#"polTuple") |",";
      resultString =  resultString | "polynomialTuple:= " | writePolynomialTupleInGAP(polSet#"polTuple") |"" ;
      -- todo: idealTerms,
      -- todo: ideal
      -- todo: idealRing
      resultString = resultString |  ")";
    return resultString;
)




--idee: liefert String fuer variablenname; Problem: variable muss lokal deklariert werden. 
writePolynomialConstructOptionsInGAP=method();
writePolynomialConstructOptionsInGAP( PolynomialConstructOptions  ) := (options)->
(
     resultString := " rec(";
     resultString =  resultString | "minChar := "      | toString convertValueToGap( options#"minChar") | "\n";
     resultString =  resultString | ", maxChar := "      | toString convertValueToGap( options#"maxChar")| "\n";
     resultString =  resultString | ", minExamples := "  | toString convertValueToGap( options#"minExamples")| "\n";
     resultString =  resultString | ", maxExamples := "  | toString convertValueToGap( options#"maxExamples")| "\n";
     resultString =  resultString | ", parallelize := "  | toString   options#"parallelize"| "\n";   
     resultString = resultString | ")";
    return ( resultString) ;
)


RFSToGAPString = method();
RFSToGAPString (RFSProblem, PolynomialConstructOptions, HashTable) :=  (rfsProblem, options, polSetTable)->
(
    for key in keys polSetTable do
    (
        assert (class key===ZZ);
        assert ( isPrime key);
    );
    resultString := "# getRFS := function() \n" ;
    resultString =  resultString | "\t local RFS, problem, rfsPolynomialSetTable,polRing,polSetList,polSet,ind,t,s,ZZPolRing,ZZPolynomialRing,ZZInd  ;\n";

     resultString =  resultString | "\t  RFS := rec();\n";

    resultString =  resultString | "\t  problem := " | writeRFSProblemInGAP(rfsProblem) | ";\n" ;

    resultString =  resultString | "\t  RFS.rfsProblem := problem ;\n";
    
    -- resultString =  resultString | "\t RFS.options := " | writePolynomialConstructOptionsInGAP(options) |";\n" ;

     resultString =  resultString | "\t  rfsPolynomialSetTable :=rec(); \n";
    
    for key in keys polSetTable do
    (
        resultString =  resultString | "\t  polSetList :=[];\n";

        if (#polSetTable#key>0) then 
        (
            polRing := ring polSetTable#key#0#"polTuple";
            characteristic:= char polRing;
            assert( isQuotientOf(ZZ,coefficientRing polRing) );
            assert( isPrime(characteristic));
            assert( isPrime((coefficientRing polRing).order) );
            assert (#(gens polRing)==2);
            s:=null;  t:=null;
            --  Da das GAP-Programm die lokalen Variablen 's' und 't' reserviert, wurde modPolRing konstruiert , 
            --   damit die erste ringVariable immer t und die zweite immer s heisst (hauptsache immer gleich für alle Ringe).   
            -- Man könnte auch die ursprünglichen Variablennamen von polRing behalten, das würde aber etwas mehr Arbeit kosten: 
            -- es müsste in der Funktion getRFS  eine Unterfunktion 'getPolSetList()' definiert werden, in der dann lokale Variablen entsprechend den Variablennamen im 'polRing' deklariert werden.
            -- Aber wieso würde man es überhaupt wollen, die ursprunglichen Variablennamen zu behalten?
            modPolRing := (ZZ/(char polRing))[symbol t, symbol s];

            niceModPolRing := (ZZ/(char polRing))[symbol t, symbol s];

            resultString =  resultString | "\t   polRing := " | writePolynomialRingInGAP(modPolRing) |";\n";
            rngGens:=gens modPolRing;
            --
            resultString =  resultString | "\t  ind:=IndeterminatesOfPolynomialRing(polRing);\n";
           

            resultString =  resultString | "\t   ZZPolynomialRing := " | writeNicePolynomialRingInGAP(niceModPolRing) |";\n";
            niceRngGens := gens niceModPolRing;
            --
            resultString =  resultString | "\t  ZZInd:=IndeterminatesOfPolynomialRing(ZZPolynomialRing);\n";
        

            for polSet in polSetTable#key do
            (
                resultString =  resultString | "\t polSet:=rec();\n";
                resultString =  resultString | "\t polSet.rfsProblem := problem; \n" ;
                resultString =  resultString | "\t polSet.polynomialRing := polRing; \n" ;
    
                polTuple := deepCopy (polSet#"polTuple");
                for polynomialInfo in polTuple do
                (
                    --  da das GAP-Programm die lokalen variablen s und t reserviert, wurde modPolRing konstruiert damit die erste ringVariable immer t und die zweite immer s heisst (hauptsache immer gleich für alle Ringe).
                    polynomialInfo#"pol" = sub( polynomialInfo#"pol",{(gens polRing)#0=>(gens modPolRing)#0,(gens polRing)#1=>(gens modPolRing)#1});
                    
                );
                for pos in 0..#(rngGens)-1 do
                (
                    resultString =  resultString | "\t " | toString (rngGens)#pos  | ":=ind[" | toString (pos+1) | "];\n";
                );
                resultString =  resultString | "\t polSet.polynomialTuple:= " | writePolynomialTupleInGAP(polTuple) |";\n" ;

                polTuple = deepCopy (polSet#"polTuple");
                for polynomialInfo in polTuple do
                (
                    --  da das GAP-Programm die lokalen variablen s und t reserviert, wurde modPolRing konstruiert damit die erste ringVariable immer t und die zweite immer s heisst (hauptsache immer gleich für alle Ringe).
                    polynomialInfo#"pol" = sub( polynomialInfo#"pol",{(gens polRing)#0=>(gens niceModPolRing)#0, (gens polRing)#1=>(gens niceModPolRing)#1} );
                    
                );
    

                for pos in 0..#(niceRngGens)-1 do
                (
                    resultString =  resultString | "\t " | toString (niceRngGens)#pos  | ":=ZZInd[" | toString (pos+1) | "];\n";
                );
                resultString =  resultString | "\t polSet.polynomialTupleZZLift:= " | writePolynomialTupleInGAP(polTuple) |";\n" ;

                resultString =  resultString | "\t Append (polSetList,[polSet]); \n";
            );

        );
        resultString =  resultString | "\t rfsPolynomialSetTable." |toString key | " := polSetList ;\n";
    );
    resultString =  resultString | "\t RFS.polynomialSetTable := rfsPolynomialSetTable ;\n";
    resultString =  resultString | "\t return RFS; \n# end; \n";
    --resultString =  resultString  | "#" | resultVariableName | " := getRFS(); ";
    return resultString;
)

complexNumberToString = method();
complexNumberToString (CC) := (cnum)->
(
    resultString:="";
    if (imaginaryPart(cnum)>=0 ) then 
        resultString=   toExternalString realPart(cnum) | "+" | toExternalString imaginaryPart(cnum) | "*ii "
    else
         resultString=   toExternalString realPart(cnum) | toExternalString imaginaryPart(cnum) | "*ii ";

    resultString = replace( "p" | toString (precision cnum) ,"",resultString);

    return resultString;
)

 
complexNumberToString (Thing) := (cnum)->
(
    if cnum===infinity then 
        return "infinity"
    else 
        assert(false);
)

transformPolynomialStringToGAPFloat=method();
transformPolynomialStringToGAPFloat(String):=(polString)->
(
       return replace("\\*ii","i",polString);    
)

transformPolynomialStringToGAPFR=method();
transformPolynomialStringToGAPFR(String):=(polString)->
(
       return replace("ii","COMPLEX_I",polString);
)

getGAPComplexFieldString =()->
(
    return "FLOAT_PSEUDOFIELD";
    --return "COMPLEX_FIELD";
)
transformPolynomialStringToGAP=method();
transformPolynomialStringToGAP(String):=(str)->
(
    --return transformPolynomialStringToGAPFR(str);
    return transformPolynomialStringToGAPFloat(str);
)

printPreimageListsToGAPString = method();
 
printPreimageListsToGAPString (Thing) := ( solution )->
(

	firstEntry := false; 
  	resultString :=  " [ ";

        firstShape:=true;
        for    pos in 0..#solution-2 do
        (
            rootEntries := solution#pos;
            if not firstShape then 
                    resultString = resultString | " ,\n"
            else
                firstShape=false;

            resultString = resultString |  "  [";
            firstEntry =true;
    
            for rootEntry in rootEntries do
            (
                  if not firstEntry then 
                    resultString = resultString | " ,"
                else
                    firstEntry=false;
               resultString = resultString | "[" | transformPolynomialStringToGAPFloat (complexNumberToString(rootEntry#0) ) |"," | (toString (rootEntry#1)) | "]"
            );
            resultString = resultString |  "  ]";
        );
        resultString = resultString |  "]";
        
        return resultString;
)

printScalingListToGAPString := method();
printScalingListToGAPString (Thing) := ( solution )->
(
  	resultString :=    " [ ";

	rootEntries := solution#(#solution-1);

	firstEntry :=true;
	for rootEntry in rootEntries do
	(
	  if not firstEntry then 
	    resultString = resultString | " ,"
	else
	    firstEntry=false;
	 resultString = resultString |   transformPolynomialStringToGAPFloat (complexNumberToString(rootEntry)) ;
	);
	resultString = resultString |  "  ] ";     
        return resultString;
)

printFullSolutionListsToGAPString=method();
printFullSolutionListsToGAPString (RFSPolynomialSet) := ( polSet )->
(

    resultString:= " [";
    firstSolution:=true;
    firstEntry:=null;

    for solution in  polSet#"fullSolutionList" do
    (
        entryPos:=0;

        if not firstSolution then 
            resultString = resultString | " ,\n"
        else
            firstSolution=false;
	resultString = resultString |  "rec ( ";
        resultString = resultString |  "  preimageLists := " | printPreimageListsToGAPString(solution) | ",";
        resultString = resultString |  "  scalingFactorList   := " | printScalingListToGAPString(solution) ;
        resultString = resultString |  " ) ";
    );
    resultString = resultString |  " ] ";
     
    return resultString;
)
 

RFSLiftedPolSetToGAPString = method();
RFSLiftedPolSetToGAPString (RFSPolynomialSet, Thing) :=  ( polSet, liftOptions   )->
(
  
    resultString := "";
    resultString =  resultString | "#LoadPackage(\"FR\"); \n" ;
    resultString =  resultString | "#LoadPackage(\"float\"); \n" ;

    resultString =  resultString | "#SetFloats(MPC);; \n" ;



    --resultString  =  resultString | "# getRFSLiftedPolSet := function() \n" ;

    resultString =  resultString | "\t local  rfsProblem,  polRing,polSetList,polSet,ind,t,s,ZZPolRing,ZZInd,liftedPolynomialRing  ;\n";

    resultString =  resultString | "\t  rfsProblem := " | writeRFSProblemInGAP(polSet#"rfsProblem") | ";\n" ;
 

    polRing := ring polSet#"polTuple";
    characteristic:= char polRing;
    assert( isQuotientOf(ZZ,coefficientRing polRing) );
    assert( isPrime(characteristic));
    assert( isPrime((coefficientRing polRing).order) );
    assert (#(gens polRing)==2);
    s:=null;  t:=null;

    --  Da das GAP-Programm die lokalen Variablen 's' und 't' reserviert, wurde modPolRing konstruiert , 
    --   damit die erste ringVariable immer t und die zweite immer s heisst (hauptsache immer gleich für alle Ringe).   
    -- Man könnte auch die ursprünglichen Variablennamen von polRing behalten, das würde aber etwas mehr Arbeit kosten: 
    -- es müsste in der Funktion getRFS  eine Unterfunktion 'getPolSetList()' definiert werden, in der dann lokale Variablen entsprechend den Variablennamen im 'polRing' deklariert werden.
    -- Aber wieso würde man es überhaupt wollen, die ursprunglichen Variablennamen zu behalten?
    modPolRing := (ZZ/(char polRing))[symbol t, symbol s];

    niceModPolRing := (ZZ/(char polRing))[symbol t, symbol s];

    resultString =  resultString | "\t   polRing := " | writePolynomialRingInGAP(modPolRing) |";\n";
    rngGens:=gens modPolRing;
    --
    resultString =  resultString | "\t  ind:=IndeterminatesOfPolynomialRing(polRing);\n";
    

    resultString =  resultString | "\t   ZZPolRing := " | writeNicePolynomialRingInGAP(niceModPolRing) |";\n";
    niceRngGens := gens niceModPolRing;
    --
    resultString =  resultString | "\t  ZZInd:=IndeterminatesOfPolynomialRing(ZZPolRing);\n";
     
    resultString =  resultString | "\t polSet:=rec();\n";
    resultString =  resultString | "\t polSet.rfsProblem := rfsProblem; \n" ;
    resultString =  resultString | "\t polSet.polynomialRing := polRing; \n" ;

    polTuple := deepCopy (polSet#"polTuple");
    for polynomialInfo in polTuple do
    (
        --  da das GAP-Programm die lokalen variablen s und t reserviert, wurde modPolRing konstruiert damit die erste ringVariable immer t und die zweite immer s heisst (hauptsache immer gleich für alle Ringe).
        polynomialInfo#"pol" = sub( polynomialInfo#"pol",{(gens polRing)#0=>(gens modPolRing)#0,(gens polRing)#1=>(gens modPolRing)#1});
        
    );
    for pos in 0..#(rngGens)-1 do
    (
        resultString =  resultString | "\t " | toString (rngGens)#pos  | ":=ind[" | toString (pos+1) | "];\n";
    );
    resultString =  resultString | "\t polSet.polynomialTuple:= " | writePolynomialTupleInGAP(polTuple) |";\n" ;

    polTuple = deepCopy (polSet#"polTuple");
    for polynomialInfo in polTuple do
    (
        --  da das GAP-Programm die lokalen variablen s und t reserviert, wurde modPolRing konstruiert damit die erste ringVariable immer t und die zweite immer s heisst (hauptsache immer gleich für alle Ringe).
        polynomialInfo#"pol" = sub( polynomialInfo#"pol",{(gens polRing)#0=>(gens niceModPolRing)#0, (gens polRing)#1=>(gens niceModPolRing)#1} );
        
    );


    for pos in 0..#(niceRngGens)-1 do
    (
        resultString =  resultString | "\t " | toString (niceRngGens)#pos  | ":=ZZInd[" | toString (pos+1) | "];\n";
    );
    resultString =  resultString | "\t polSet.polynomialTupleZZLift := " | writePolynomialTupleInGAP(polTuple) |";\n" ;

    idealRing:= ring polSet#"solutionIdeal";

    idealRngGens := gens idealRing;
    idealRngGens  = delete (commonVariable idealRing , idealRngGens);
    idealRngGens = delete (homogenVariable idealRing , idealRngGens);

    idealRngGens =sort idealRngGens;

    resultString    =  resultString | " liftedPolynomialRing:= PolynomialRing(  " | getGAPComplexFieldString() |    " ,[\"" | toString (commonVariable idealRing) | "\","  |   " \"" | toString (homogenVariable idealRing) | "\"] : new );\n" ;

    --resultString    =  resultString | " liftedPolynomialRing:= PolynomialRing(  " | getGAPComplexFieldString() | " ,\"" | toString (commonVariable idealRing) | "\" : new );\n" ;
    resultString =  resultString | "\t polSet.liftedPolynomialRing:= liftedPolynomialRing;\n ";
      
    resultString =  resultString | "\t  ind:=IndeterminatesOfPolynomialRing(liftedPolynomialRing);\n";
    resultString =  resultString | "\t "  | toString (commonVariable idealRing) |" := ind[1];\n";
    resultString =  resultString | "\t "  | toString (homogenVariable idealRing) |" := ind[2];\n";

    resultString =  resultString | "\t polSet.decimalPrecision := " | toString liftOptions#"decimalPrecision" |";\n" ;

    complexRing:=null;

    idealRing = polSet#"solutionComplexRing";

    -- TODO Macaulay2 question: how to replace coefficientRing

     resultString =  resultString | "\t polSet.rootData := " |   printFullSolutionListsToGAPString(polSet) | ";\n" ; 

    -- erzeuge IdealRing
      
    resultString =  resultString | "\t return polSet; \n #end; \n";
    --resultString =  resultString | "#" | resultVariableName | " := getRFSLiftedPolSet(); ";
    return resultString;
)



-- todo: check for file existence and do not overwrite existing files!

saveFFRFSResultInGAPfile = method();
saveFFRFSResultInGAPfile( RFSProblem, PolynomialConstructOptions,MutableHashTable,String) := ( rfsProblem, options, rfsPolSetTable,fileName)->
(
    --fileName:= outputdest#0;
    --variableName:= outputdest#1;
    ofile := openOut (fileName);
    resultString := RFSToGAPString(rfsProblem, options, rfsPolSetTable);
    ofile << resultString << close;
    return;
)


saveRFSLiftResultInGAPfile = method();
saveRFSLiftResultInGAPfile( RFSPolynomialSet, Thing,String) := (polSet, liftOptions, fileName)->
(
    ofile := openOut (fileName);
    resultString := RFSLiftedPolSetToGAPString( polSet,liftOptions );
    ofile << resultString << close;
    return;
)


