
-- Experiments ,  examples and tests


get43222Equations=()->
(
    -- so geht das nicht.
    a:=symbol a;
    b:=symbol b;
    c:=symbol c;
    z:=symbol z;
    --mons := monoid [ a_1..a_5, b_1..b_5, c_1..c_5, z, Degrees=>{1,1,3,2,1,1,1,3,2,1,1,1,3,2,1,1} ];
    SZ := ZZ[  a_1..a_5,  b_1..b_5,  c_1..c_5,  z, Degrees=>{1,1,3,2,1,1,1,3,2,1,1,1,3,2,1,1} ];
    FZ := (z-a_1)^4*(z-a_2)^3*(z^3+a_3*z^2+a_4*z+a_5)^2; 
    GZ := 2*(z-b_1)^4*(z-b_2)^3*(z^3+b_3*z^2+b_4*z+b_5)^2; 
    HZ := (z-c_1)^4*(z-c_2)^3*(z^3+c_3*z^2+c_4*z+c_5)^2 ;
    return (FZ-GZ+HZ);
)

get43222Ideal=()->
(
    eqn:=get43222Equations();
    z:=(gens ring eqn)#15;
    ideal last coefficients(eqn, Variables=>z)
)


unknownAppearsInPoly=method();
unknownAppearsInPoly(RingElement,RingElement):= Boolean=> (polynomial,unknown)->
(
    polynomialVariables := apply(flatten entries first coefficients polynomial,el->(factor el)#0#0);
    return ( #(select(polynomialVariables,(var)->(unknown===var)))>0);
)

oneUnknownAppearsInPoly=method();
oneUnknownAppearsInPoly(RingElement,List):= Boolean=> (polynomial,unknownList)->
(
    polynomialVariables := apply(flatten entries first coefficients polynomial,el->(factor el)#0#0);
    for unknown in unknownList do
        if (unknownAppearsInPoly(polynomial,unknown)) then 
            return true;
    return false;
)

get43222EquationsNew=(baseRing)->
(
	a:=symbol a;
	b:=symbol b;
	c:=symbol c;
	l:=symbol l;
	s:=symbol s;
	t:=symbol t;
	--RZ = baseRing[  a_2..a_5,  b_2..b_5,  c_2..c_5,  l  ];
	--SZ = baseRing[t,s];
	--RSZ := RZ**SZ;
	SZ := baseRing[  a_2..a_5,  b_2..b_5,  c_2..c_5,  l,t,s  ];
    
	FZ :=l*(  s)^4*(t+a_2*s)^3*(t^3+a_3*t^2*s+a_4*t*s^2+a_5*s^3)^2; 

    
    
	GZ := (t-s)^4*(t+b_2*s)^3*(t^3+b_3*t^2*s+b_4*t*s^2+b_5*s^3)^2;
	HZ := (t  )^4*(t+c_2*s)^3*(t^3+c_3*t^2*s+c_4*t*s^2+c_5*s^3)^2;
    
    --FZfactorsByExponent:= new MutableHashTable;
    --for fact in factor FZ do
    --    FZfactorsByExponent#(fact#1)=fact#0;

    --FZfactors:= factor FZ;


	FZ-GZ+HZ
)



get43222IdealNew=(baseRing)->
(
    eqn:=get43222EquationsNew(baseRing);
    t:=(gens ring eqn)#13;
    s:=(gens ring eqn)#14;
    tmpIdeal := ideal last coefficients(eqn, Variables=>{s,t});
   ReducedRing := baseRing[ (gens ring tmpIdeal)_{0..12} ];
   sub(tmpIdeal,ReducedRing)
)



example43222SingleVariableLift=(firstVariableIdx,secondVariableIdx)->
(
    solutionIdeal := get43222Ideal();

    SZ:= ring solutionIdeal;

    solutionIdeal=sub(solutionIdeal,(gens SZ)#0=>-4);
   -- solutionIdeal=sub(solutionIdeal,(gens SZ)#5=>1);
    solutionIdeal=sub(solutionIdeal,(gens SZ)#10=>5);
    
    JZ := jacobian solutionIdeal;

    
    solutionChar := 11;
  solution11 := matrix{ {-4,0,2,-3,3,   1,-2,5,-3,1,     5,-1,5,2,-5,   0} };
    solution11 = sub(solution11, ZZ/solutionChar);
    assert( sub(solutionIdeal, solution11) == 0 );


    assert ( rank (sub ( jacobian solutionIdeal, solution11))== numColumns JZ);

    liftOptions:= new LiftOptions;
    liftOptions#"maxLatticeDim" = 79;
    liftOptions#"initialLatticeDim"=79;
    unknown := (gens SZ)#firstVariableIdx; 
    if (secondVariableIdx=!=null) then 
      unknown = unknown +  (gens SZ)#secondVariableIdx; 
    liftResult := computeSingleMinPoly( solutionIdeal, solution11, unknown,unknown, "options"=>liftOptions);
    

    fileName:="43222_unknown_";
    if (secondVariableIdx===null) then 
        fileName = fileName | (toString firstVariableIdx) | ".m2"
    else 
        fileName = fileName | "(" | (toString firstVariableIdx)  |","|  (toString secondVariableIdx) | ").m2";


    resultFile:= openOut(fileName);

    
    resultFile << "liftResult:= { (" << firstVariableIdx << "," <<  secondVariableIdx <<")," << (toExternalString (liftResult.polynomial)) << "};";
    resultFile << close;
)


testPadicLift=()->
(
    x:=null;
    y:=null;
    x=symbol x;
    y=symbol y;
    rng:=ZZ[x,y];
    x = (gens rng)#0;
    y = (gens rng)#1;
    FZ1 := 33*x^3+19*x^2-81*x-4;
    FZ2 := y-1;
    id := ideal ({FZ1,FZ2} );
    Fp:= ZZ/11;
    solution := matrix {{ 1_Fp,1_Fp } };
    liftResult := liftPoint( id,  solution, 1);
    nextLiftResult := liftPoint( id,  solution, 2);

    dummy:=null;

    liftOptions := createLiftOptions( dummy );

    liftOptions.verbose=true;
    
    liftResult := liftPoint( id,  solution, 12);
    nextLiftResult := liftPoint( id,  solution, 13);

    liftResult := liftPoint( id,  solution, 3);
    nextLiftResult := liftPoint( id,  solution, 4);

    lllResult := tryLLLReduction(x,liftResult, nextLiftResult, "reductionOpts"=>liftOptions);
    lllResult.foundLiftCandidate
)

 
-- updated 2.1.2013
tryingLift43222New=()->
(
    --  loadPackage "padicLift";
	IZ = get43222IdealNew(ZZ);
  

	--
	solutionChar := 11;
	solutionPoint := matrix{{ -5,3,2,3,   -3,0,-2,-3,   3,0,-3,-5,  4}};
	solutionPoint = sub(solutionPoint, ZZ/solutionChar);
    assert( sub(IZ, solutionPoint) == 0 );
    --
    liftOptions:= new LiftOptions;
    liftOptions#"maxLatticeDim" = 7;
    liftOptions#"verbose"=true;
    generatorList := gens ring IZ;
    unknownList := generatorList_{0..(#generatorList-3)};
    --
    (pollist, liftInfo) := computeMinPolys(IZ, solutionPoint, unknownList, "options"=>liftOptions);
    compatibilityUnknownList := apply(#unknownList -1, currvarIdx->( (unknownList)#0 + (unknownList)#(currvarIdx+1)));
    (polcomplist,compatLiftInfo) := computeMinPolys(IZ, solutionPoint, compatibilityUnknownList,  "options"=>liftOptions);

	--
	print toString new Array from pollist;
	print toString new Array from polcomplist;

    complexSolutionData := approxComplexSolutions(IZ, solutionPoint, "options"=>liftOptions);

    IC = get43222IdealNew(CC);
    rootList:=complexSolutionData#"approxVanishingSetElems";
    --check:
   complexPseudoField := ring rootList#0;
   complexPolyRing := ring rootList#0[ gens ring IC ] ;
   sub(gens IC, sub( rootList#0, complexRing ));


    -- apply(rootList,root-> (subMatrix := sub(gens ring IC,rootList ); max flatten entries subMatrix));

    residue := abs sub(max flatten apply(rootList, root->flatten entries sub(gens IC, sub( root, complexRing ))),complexPseudoField);

    
)


tryingLift43222NewPair=()->
(
    --  loadPackage "padicLift";
    IZ := get43222IdealNew(ZZ);
    IC := get43222IdealNew(CC);
    --
    solutionChar := 11;
    solutionPoint := matrix{{ -5,3,2,3,   -3,0,-2,-3,   3,0,-3,-5,  4,  0,  0}};
    solutionPoint = sub(solutionPoint, ZZ/solutionChar);
    assert( sub(IZ, solutionPoint) == 0 );
    --
    liftOptions:= new LiftOptions;
    liftOptions#"maxLatticeDim" = 7;
    liftOptions#"verbose"=true;
    generatorList := gens ring IZ;
    unknownList := generatorList_{0..(#generatorList-3)};
    --
    complexSolutionData  := approxComplexSolutions(IZ, solutionPoint, unknownList, "options"=>liftOptions);

    rootList:=complexSolutionData#"approxVanishingSetElems";
    --check:
    -- apply(rootList,root-> (subMatrix := sub(gens ring IC,rootList ); max flatten entries subMatrix))
    --
    print toString new Array from pollist;
)

--M2 errors; got an dublicate large block deallocation

tryingLift43222=()->
(
	-- restart;
	--  load "lift solution.m2";
	IZ := get43222Ideal();

	IZ =sub(IZ,(gens ring IZ)#0=>-4);
   -- IZ=sub(IZ,(gens ring IZ)#5=>1);
    IZ=sub(IZ,(gens ring IZ)#10=>5);
	
	JZ := jacobian IZ;
    

	solutionChar := 11;
	solutionPoint := matrix{ {-4,0,2,-3,3,   1,-2,5,-3,1,     5,-1,5,2,-5,   0} };
	solutionPoint = sub(solutionPoint, ZZ/solutionChar);

    rank (sub ( jacobian IZ, solutionPoint));

    assert( sub(IZ, solutionPoint) == 0 );

	--betti gens IZ

    liftOptions:= new LiftOptions;
     --liftOptions#"maxLiftDepth"=>11;
    liftOptions#"initialLatticeDim"=79;
    liftOptions#"maxLatticeDim" = 79;
    
    generatorList := gens ring IZ;
    unknownList := generatorList_{0..(#generatorList-3)};

    (pollist, liftInfo) := computeMinPolys(IZ,solutionPoint,unknownList, liftOptions);
    
    compatibilityUnknownList := apply(#unknownList -1, currvarIdx->( (unknownList)#0 + (unknownList)#(currvarIdx+1)));
    (polcomplist,compatLiftInfo) := computeMinPolys(IZ, solutionPoint, compatibilityUnknownList, liftOptions);
	
	print toString new Array from pollist;
	print toString new Array from polcomplist;
)

----------

end

---(ZZ/11)[x]
--preW2 = (3)*x^3 + (7)*x^5 + (5)*x^6 + (10)*x^7 + (3)*x^8 + (7)*x^9 + (3)*x^10 + (4)*x^11 + (1)*x^12 + (1)*x^13
--preW1 = (4)*x^0 + (10)*x^1 + (3)*x^2 + (3)*x^3 + (6)*x^4 + (4)*x^5 + (5)*x^6 + (3)*x^7 + (1)*x^8 + (7)*x^9 + (1)*x^10
--preW3 = x^13+x^12+4*x^11-3*x^10-2*x^9-3*x^8+3*x^7-3*x^6+5*x^5-3*x^4-4*x^3+4*x^2-5*x-2
-- W2= (t)^3*(t-1*s)^4*(t^3-3*t^2*s-t*s^2+5*s^3)^2
-- W1 = (s)^3*(t-2*s)^4*(t^3+2*t^2*s-3*t*s^2-5*s^3)^2
-- W3= (t+1*s)^4*(t+4*s)^3*(t^3-2*t^2*s+3*t*s^2+1*s^3)^2

liftAndPair43222Equations=()->
(
    -- restart
   loadPackage ("rationalFunctionSearch" );

    debug rationalFunctionSearch;

    solutionChar := 11;
    rng:=createRFSRing(solutionChar);

    t := commonVariable rng;
    s := homogenVariable rng;

    shape:= new Shape from {4,3,2,2,2};
    shapeList:= new RFSShapeList from {shape,shape,shape};

    rfsProblem := createRFSProblem (shapeList);

    W2 = (t)^4  *( t +3*s )^3*( t^3 -3*t*s^2 -5*s^3 )^2   
    W1 = (s)^4  *( t -5*s )^3*( t^3 +3*t^2*s +2*t*s^2 +3*s^3 )^2 
    W3 = (t-s)^4*( t -3*s )^3*( t^3 -2*t*s^2 -3*s^3 )^2

    polSet43222   :=  createRFSPolynomialSet( rfsProblem, { W2, W1, W3 } );
    polSet43222   :=  createRFSPolynomialSet( rfsProblem, { W1, W2, W3 } );

    normalizePolynomialSetInPlace(polSet43222);

    assert( IsFullNormalized( polSet43222) );
   
    ( IZ, solutionPoint, equations, scalingVariableList ) := createLiftInputData(polSet43222,3);

    assert( sub(IZ, solutionPoint) == 0 );

    liftOptions:= new LiftOptions;
    liftOptions#"maxLatticeDim" = 7;
    liftOptions#"verbose"=true;

    liftOptions#"decimalPrecision"= 16;

    tryLiftAndLLLAndPairPolSet(polSet43222, "options"=>liftOptions);

    computeMinPolys(polSet43222#"ideal", solutionPoint, polSet43222#"unknownVariableList", "options"=>liftOptions);

    unknown= polSet43222#"unknownVariableList"#0;

    liftres = computeSingleMinPoly( polSet43222#"ideal", solutionPoint, unknown, unknown, "options"=>localLiftAndLLLOptions );

   
    eps := max flatten apply( apply(polSet43222#"rootList",root->sub(gens IZ,root)),el->flatten entries el);
      print eps;

    decimalPrecision= liftOptions#"decimalPrecision" ; --16
    solutionList := vanishedSetToRFSSolution (polSet43222);
    
    sub( polSet43222#"solutionEquationsDebug"#0 , matrix { polSet43222#"solutionList"#0|{commonVar,homVar}});

    sub( polSet43222#"solutionEquationsDebug"#0, rngGens#0=>polSet43222#"solutionList"#0#0);

  
    

    sub(gens polSet43222#"solutionIdeal",matrix {polSet43222#"solutionList"#0|{1,1}})

    sub(gens polSet43222#"solutionIdeal",matrix {polSet43222#"solutionList"#0|{1,1}})

    rng:=ring polSet43222#"solutionEquationsDebug"#0;

    rng:=ring polSet43222#"solutionIdeal"
    
    rngGens=gens rng;

    commonVar:=commonVariable rng;
    homVar:= homogenVariable rng;

    newGens := sub (gens polSet43222#"solutionIdeal",homVar=>1);

    sub(newGens,matrix {polSet43222#"solutionList"#0|{1,1}})

    
    cc2 = map(rng,rng,matrix{ polSet43222#"solutionList"#0|{commonVar,homVar}});

    last coefficients cc2( polSet43222#"solutionEquationsDebug"#0); -- same as ...


    factor polSet43222#"polTuple"#0#"solutionIdealTerm"
 
)



--  debug rationalFunctionSearch
-- printFullSolutionListsToGAPString(polSet)

liftAndPair43222EquationsForGap=()->
(
    -- restart xxxxxx

   loadPackage ("padicLift" );

    loadPackage ("rationalFunctionSearch" );
 
 
    --debug padicLift;

    solutionChar := 11;
    rng:=createRFSRing(solutionChar);

    t := commonVariable rng;
    s := homogenVariable rng;

    shape:= new Shape from {4,3,2,2,2};
    shapeList:= new RFSShapeList from {shape,shape,shape};

    rfsProblem := createRFSProblem (shapeList);

    W2 = (t)^4  *( t +3*s )^3*( t^3 -3*t*s^2 -5*s^3 )^2   --0
    W3 = (t-s)^4*( t -3*s )^3*( t^3 -2*t*s^2 -3*s^3 )^2 --1
    W1 = (s)^4  *( t -5*s )^3*( t^3 +3*t^2*s +2*t*s^2 +3*s^3 )^2 --infty
    

    polSet   :=  createRFSPolynomialSet( rfsProblem, [ W2, W1, W3 ] );        
   
    liftOptions:= new LiftOptions;
    liftOptions#"maxLatticeDim" = 7;
    liftOptions#"decimalPrecision" = 16;

    
    tryLiftAndLLLAndPairPolSet( polSet, "options"=>liftOptions );

    debug rationalFunctionSearch  
    RFSLiftedPolSetToGAPString(polSet, liftOptions,"varName");

    saveRFSLiftResultInGAPfile  (polSet, liftOptions,"43222LiftResult.gap","varName");

)

saveRootList=(filePrefix,filePostfix,rootList)->
(
    pos:=0;
    for pos in 0..#rootList-1 do
    (
        roots:=flatten entries rootList#pos;
        fileName:=filePrefix | ".sol" |toString(pos)|filePostfix;
        saveRoots(fileName,roots);
    )
)

-- works only for the 43222 example...
saveSolutionList =(filePrefix,filePostfix,solutionList)->

(
    pos:=0;
    for pos in 0..#rootList-1 do
    (
        solution :=  solutionList#pos_{1..4} | solutionList#pos_{6..9} | solutionList#pos_{11..15} |{1,1};
        fileName:=filePrefix | ".sol" |toString(pos)|filePostfix;
        saveRoots(fileName,solution);
    )
)

saveRoots=( fileName, roots )->
(
    f:=openOut(fileName);
    --# convert to complex and real part:
    --crroots := flatten apply(#roots-2, rootPos->{ realPart(roots#rootPos),imaginaryPart(roots#rootPos) });
    crroots := flatten apply(#roots, rootPos->{ realPart(roots#rootPos),imaginaryPart(roots#rootPos) });
    --
    sroots := apply(crroots,r->toExternalString r);
    sroots = new MutableList from sroots;
    print sroots;
    for pos in 0..#sroots-1 do
    (
        pos1 := regex("p",sroots#pos);
        assert(pos1=!=null);
        tmp = substring(0, pos1#0#0, sroots#pos);
        --
        pos1 := regex("e",sroots#pos);
        if (pos1=!=null) then 
            tmp = tmp | substring( pos1#0#0, sroots#pos);
        sroots#pos = tmp;
    );
    --
    apply(sroots, root->(f << root << " " ));
    f << close;
)

----------

 RZ = ZZ[symbol x,symbol y];
            FZ = (33*x^3+19*x^2-81*x-4)*y;          
            IFZ = ideal FZ; 
     K = ZZ/3; RK =K[symbol x,symbol y]; 
            IFK =sub(IFZ,RK)
              allPoints = flatten apply((char RK),x->apply(char RK, y->matrix {{ x_K, y_K }})); 
            --select the vanishing set of ideal IFK from all points in RK -- stand vorher als Text; finde ich aber unnoetig.
            solutions = select (allPoints,(point)->( sub( IFK,point) == 0) )  
             liftCapablePointList = select (solutions,(point)->( JFp = sub( jacobian IFZ,point); rank JFp==numColumns JFp )) 
               solutionPoint = liftCapablePointList#1
        capableUnknownList = select(gens ring IFZ, (unknown)->( sub (diff(unknown, FZ), solutionPoint)!=0 ) )
            unknown = capableUnknownList#0;
            ( liftAndLLLResult , liftInfo )  = computeMinPolys  ( IFZ, solutionPoint, {unknown} );

-- sandbox: check options

testOptionParameter = method(Options=>{(symbol opts)=>"bla"})
--testOptionParameter = method(Options=>{"opts2"=>"bla"})
testOptionParameter (String) := String => opts-> (str) ->
(
    print opts.opts;
)
------------
-- sandbox:  test substitute behaviour

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
RZ = ZZ[x,y]
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

FZ= sub (F,RZ);
IF = ideal F
IFp = ideal Fp
IFpZ = ideal sub (Fp,RZ)

IFZ = ideal FZ
JFZ = jacobian IFZ

solution1 = matrix{{1_K,1_K}} 
solution2 = matrix{{5_K,1_K}}  

sub(solution11,K);
sub(

sub(IFZ,solution11)
liftDepth = 4
liftResult = liftPoint( IF, solution11, liftDepth );
liftResult = liftPoint( IFZ, solution11, liftDepth );

liftResult = liftPoint( IFpZ, solution1, liftDepth );
liftResult = liftPoint( IFpZ, solution2, liftDepth );

apply(liftResultList,lres ->sub(IFZ,lres))
liftResult=liftResultList#(liftDepth-1)

liftoptions= new LiftOptions
computeSingleMinPoly (IFZ, solution11, (gens ring IFZ)#0,liftoptions)
liftResult1 = computeSingleMinPoly (IFZ, solution1, (gens ring IFZ)#0,liftoptions)
liftResult2 = computeSingleMinPoly (IFZ, solution2, (gens ring IFZ)#0,liftoptions)

solutionIdeal1=ideal substitute(liftResult1.polynomial,(gens ring liftResult1.polynomial)#0=>(gens RZ)#0)
solutionIdeal2=ideal substitute(liftResult2.polynomial,(gens ring liftResult2.polynomial)#0=>(gens RZ)#0)

assert ( isSubset(IFZ,solutionIdeal1) );
assert ( isSubset(IFZ,solutionIdeal2) );



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

