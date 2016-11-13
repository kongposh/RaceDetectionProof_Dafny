datatype Op = Write(tid:Tid, loc: Var)
datatype opt<T> = Just(value: T) | Nothing
datatype FtState = FtState(ts : ThreadsMap, vs: EpochMap)
datatype DjitState = DjitState(ts : ThreadsMap, vs: VarsMap)
datatype Epoch = Epoch(tid : Tid, val : Value)
type ThreadsMap = map<Tid, VC>
type VarsMap = map<Var, VC>
type EpochMap = map<Var, Epoch>
type Tid = int
type Value = int
type Var = char
type Trace = seq<Op>
type VC = seq<int>

predicate method isValidTrace(size : nat, vars : seq<char>)
{
	size > 0 && |vars| > 0 && isVarsUnique(vars)
}

predicate method isVarsUnique(vars : seq<char>)
{
	forall i,j : int :: 0 <= i < j < |vars| ==> vars[i] != vars[j]
}

predicate method isWellFormedFt(res : FtState)
//ensures isWellFormed(res) == true ==> 
{
 ensures forall i:int :: i in res.ts <==> 0 <= i < |res.ts|
}


ghost method ftStart(size : nat, vars : seq<char>) returns (res : FtState)
requires isValidTrace(size,vars)
ensures |res.ts| == size
ensures forall i:int :: i in res.ts <==> 0 <= i < |res.ts|
ensures forall j : int :: 0 <= j < size ==> |res.ts[j]| == size
ensures forall j : int :: 0 <= j < size ==> forall i : int :: 0 <= i < size ==> res.ts[j][i] == 0
ensures forall i:char :: i in res.vs <==> i in vars
//ensures test(res,vars)
ensures forall i : char :: i in res.vs ==> 0 <= res.vs[i].tid < size
ensures forall i : int :: 0 <= i < size ==> forall j : int :: 0 <= j < size ==> res.ts[i][j] == 0
ensures forall i : char :: i in res.vs ==> res.vs[i].val == 0
{
	var tmap := initThreadMap(size);
	var emap := initEpochMap(vars,size);
	res := FtState(tmap,emap);
}


ghost method djitStep (ds : DjitState, op : Op, size : nat) returns (res : opt<DjitState>)
requires size > 0
requires forall j : int :: j in ds.ts ==> |ds.ts[j]| == size 
requires forall j : char :: j in ds.vs ==> |ds.vs[j]| == size 
requires op.loc in ds.vs
requires op.tid in ds.ts
requires 0 <= op.tid < size
ensures (res.Just?) ==> forall j : int :: j in res.value.ts ==> |res.value.ts[j]| == size 
ensures (res. Just?) ==> forall j : char :: j in res.value.vs ==> |res.value.vs[j]| == size 
ensures (res.Just?) ==> op.loc in res.value.vs
ensures (res.Just?) ==> op.tid in res.value.ts
ensures (res.Just?) ==> (forall i : int :: 0 <= i < size ==> res.value.vs[op.loc][i] <= res.value.ts[op.tid][i])
ensures (res == Nothing) ==> (exists i : int :: 0 <= i < size && ds.vs[op.loc][i] > ds.ts[op.tid][i])
{
	
	match op
	case Write(tid, loc) => 
	{
		var val := djitChecker(ds.ts[tid], ds.vs[loc]);
		if(val == true)
		{
			res := Nothing;
		}
		else
		{
			//ts state
			var tmapTemp := ds.ts;
			var tvcTemp := tmapTemp[tid];
			var tvalTemp := tvcTemp[tid];
			tvcTemp := tvcTemp[tid := tvalTemp];
			tmapTemp := tmapTemp[tid := tvcTemp];
			
			// vs state
			var vmapTemp := ds.vs;
			var vvcTemp := vmapTemp[loc];
			var vvalTemp := vvcTemp[tid];
			vvcTemp := vvcTemp[tid := vvalTemp];
			vmapTemp := vmapTemp[loc := vvcTemp];
		
			// make new djit state
			var dsTemp := DjitState(tmapTemp, vmapTemp);
			res :=  Just(dsTemp);
		}
	}
}


ghost method djitChecker ( ts : VC, vs : VC) returns ( res : bool)
requires |vs| == |ts|;
ensures res == false ==> forall i : int :: 0 <= i < |ts| ==> ts[i] >= vs[i]
ensures res == true ==> exists i : int :: 0 <= i < |vs| && vs[i] > ts[i];
{
	res := false;
	var i := 0;
	while ( i < |ts|)
	invariant 0 <= i <= |ts|
	invariant res == true ==> exists j : int :: 0 <= j < i && vs[j] > ts[j];
	invariant res == false ==> forall j : int :: 0 <= j < i ==> ts[j] >= vs[j]
	{
	var t := ts[i];
	var e := vs[i];
	if( e > t )
	{
		res := true;
		//return res;
		//assert exists j : int :: 0 <= j < i ==> vs[j] > ts[j];
	}
	i := i + 1;
	}
	//assert res == false ==> forall i : int :: 0 <= i < |ts| ==> ts[i] >= vs[i];
	//assert res == true ==> exists j : int :: 0 <= j < |vs| ==> vs[j] > ts[j];
}

ghost method ftStep (fs : FtState, op : Op, size : nat) returns (res : opt<FtState>)
requires size > 0
requires op.loc in fs.vs
requires op.tid in fs.ts
requires 0 <= op.tid < size
requires forall i : char :: i in fs.vs ==> 0 <= fs.vs[i].tid < size
requires forall j : int :: j in fs.ts ==> |fs.ts[j]| == size
requires 0 <= fs.vs[op.loc].tid < size
requires fs.vs[op.loc].tid in fs.ts
requires fs.vs[op.loc].val <= fs.ts[op.tid][fs.vs[op.loc].tid]
//ensures (res.Just?) ==> (forall i : int :: 0 <= i < |fs.ts[op.tid]| ==> fs.vs[op.loc].val <= fs.ts[op.tid][i])
ensures (res.Just?) ==> forall j : int :: j in res.value.ts ==> |res.value.ts[j]| == size 
ensures (res.Just?) ==> op.loc in res.value.vs
ensures (res.Just?) ==> op.tid in res.value.ts
ensures (res.Just?) ==> res.value.vs[op.loc].tid in res.value.ts
ensures (res.Just?) ==> 0 <= res.value.vs[op.loc].tid < size
ensures(res.Just?) ==> res.value.vs[op.loc].val <= res.value.ts[op.tid][res.value.vs[op.loc].tid];
ensures (res == Nothing) ==> fs.vs[op.loc].val > fs.ts[op.tid][fs.vs[op.loc].tid];
{
	
	match op
	case Write(tid, loc) => 
	{

		
		var eid := fs.vs[loc].tid;
		
		if(fs.vs[loc].val > fs.ts[tid][eid])
		{
			res := Nothing;
		}
		else
		{
			var tmapTemp := fs.ts;
			var tvcTemp := tmapTemp[tid];
			var tvalTemp := tvcTemp[tid] + 1;
			tvcTemp := tvcTemp[tid := tvalTemp];
			tmapTemp := tmapTemp[tid := tvcTemp];

			//fs
			var emapTemp := fs.vs;
			var evalTemp := tmapTemp[tid][tid];
			var eTemp := Epoch(tid, evalTemp);
			emapTemp := emapTemp[loc := eTemp];
			var fsTemp := FtState(tmapTemp, emapTemp);
			assert fsTemp.vs[loc].val == fsTemp.ts[tid][tid];
			res := Just(fsTemp);
		}
	}
	
}	

lemma ftstep_equals_djitstep(fs : FtState, ds : DjitState, op :  Op, size :nat)
requires size > 0
requires 0 <= op.tid < size 
requires op.loc in fs.vs
requires op.tid in fs.ts
requires forall i : char :: i in fs.vs ==> 0 <= fs.vs[i].tid < size
requires forall j : int :: j in fs.ts ==> |fs.ts[j]| == size
requires fs.vs[op.loc].tid in fs.ts
requires 0 <= fs.vs[op.loc].tid < size
requires fs.vs[op.loc].val <= fs.ts[op.tid][fs.vs[op.loc].tid]
requires op.loc in ds.vs
requires op.tid in ds.ts
requires forall j : int :: j in ds.ts ==> |ds.ts[j]| == size 
requires forall j : char :: j in ds.vs ==> |ds.vs[j]| == size

requires forall i : int :: 0 <= i < size ==> ds.ts[op.tid][i] >= ds.vs[op.loc][i];

//same thread states
requires forall i : int :: 0 <= i < size ==> fs.ts[op.tid][i] == ds.ts[op.tid][i]
requires forall i : int :: 0 <= i < size ==> ds.vs[op.loc][i] <= fs.vs[op.loc].val
requires (fs.vs[op.loc].val == ds.vs[op.loc][fs.vs[op.loc].tid]);

ensures forall i : int :: 0 <= i < size ==> ds.vs[op.loc][i] <= fs.vs[op.loc].val;
ensures forall i : int :: 0 <= i < size ==> fs.ts[op.tid][i] == ds.ts[op.tid][i]
ensures forall i : int :: 0 <= i < size ==> ds.vs[op.loc][i] <= fs.vs[op.loc].val
ensures (fs.vs[op.loc].val == ds.vs[op.loc][fs.vs[op.loc].tid]);
{
	match op
	case Write(tid,loc) => {
	var ft := ftStep(fs, op, size);
	var djit := djitStep(ds,op,size);
	assert ft.Just? <==> djit.Just?;
	assert ft.Just? ==> forall i : int :: 0 <= i < size ==> ds.vs[op.loc][i] <= fs.vs[op.loc].val;
	assert ft.Just? ==> fs.vs[loc].val <= fs.ts[tid][fs.vs[loc].tid];
	assert djit.Just? ==> forall i : int :: 0 <= i < size ==> ds.ts[tid][i] >= ds.vs[loc][i];
	assert ft == Nothing <==> djit == Nothing;
	//forall i : int :: 0 <= i < size ==> res.value.vs[op.loc][i] <= res.value.ts[op.tid][i]
	}

	
	//assert ft.Just? <==> djit.Just?;
	//assert ft == Nothing <==> djit == Nothing;
}

/*lemma maxIdinTrace(trace : Trace)
requires |trace| > 0
{
		var max := getMaxId(trace);
		assert max in getIds(trace);
}*/


ghost method ft( trace : Trace, numberOfThreads : nat) returns ( res : bool )
requires |trace| > 0
requires numberOfThreads > 0
requires forall i : int :: 0 <= i < |trace| ==> 0 <= trace[i].tid < numberOfThreads
requires getMaxIdF(trace, 0, 0) in getIds(trace);
{
	var vars := getVarsM(trace);
	var maxId := getMaxIdF(trace, 0, 0);
	var fts := ftStart(numberOfThreads,vars);
	var ftres := ftStep(fts,trace[0],numberOfThreads);
	if(ftres.Just?)
	{
		res := false;
	}
	else
	{
		res := true;
	}
}

ghost method djitStart(numberOfThreads : nat, vars : seq<char>) returns (res : DjitState)
requires numberOfThreads > 0
requires |vars| > 0
requires forall i,j : int :: 0 <= i < j < |vars| ==> vars[i] != vars[j]
ensures forall i:int :: i in res.ts <==> 0 <= i < numberOfThreads
ensures forall j : int :: 0 <= j < numberOfThreads ==> |res.ts[j]| == numberOfThreads
ensures forall j : char :: j in res.vs ==> 0 < |res.vs[j]| == numberOfThreads
ensures forall j : int :: 0 <= j < numberOfThreads ==> forall i : int :: 0 <= i < numberOfThreads ==> res.ts[j][i] == 0
ensures forall i:char :: i in res.vs ==> i in vars
ensures forall i : char :: i in vars ==> i in res.vs
ensures forall i : int :: 0 <= i < numberOfThreads ==> forall j : int :: 0 <= j < numberOfThreads ==> res.ts[i][j] == 0
ensures forall i : char :: i in res.vs ==> forall j : int :: 0 <= j < |res.vs[i]| ==> res.vs[i][j] == 0
{
	var tmap := initThreadMap(numberOfThreads);
	var vmap := initVarsMap(vars,numberOfThreads);
	res := DjitState(tmap,vmap);
}

ghost method initEpochMap(vars: seq<char>, numberOfThreads : nat) returns (res : EpochMap)
requires |vars| > 0
requires numberOfThreads > 0
requires forall i,j :: 0 <= i < j < |vars| ==> vars[i] != vars[j]
//requires forall i:int :: i in tmap ==> |tmap[i].vc| == size;
//requires |tmap| == size
//requires forall i:int :: i in tmap <==> 0 <= i < size
//requires forall i :int :: 0 <= i < size ==> forall j : int :: 0 <= j < size ==> tmap[i].vc[j] == 0;
//ensures forall i:char :: i in res ==> |res[i].vc| == size;
ensures forall i:char :: i in res ==> i in vars
ensures forall i : char :: i in res ==> 0 <= res[i].tid < numberOfThreads
//ensures forall i : char :: i in res ==> prop_largest_epoch(res[i]) == true
//ensures forall i : char :: i in res ==> forall j :int :: 0 <= j < |res[i].vc| ==> res[i].vc[j] == 0
ensures forall i : char :: i in vars ==> i in res
ensures forall i : char :: i in res ==> res[i].val == 0
//ensures forall i : char :: i in res ==> res[i].epoch.val in res[i].vc
//ensures forall i : char :: i in res ==> res[i].epoch.val == res[i].vc[res[i].epoch.tid]
{
	var j := 0;
	res := map[];
	var i := 0;
	while( j < |vars| )
	invariant 0 <= j <= |vars|
	invariant forall i,j :: 0 <= i < j < |vars| ==> vars[i] != vars[j]
	invariant forall i:char :: i in res ==> i in vars
	invariant forall i: int :: 0 <= i < j ==> vars[i] in res
	invariant forall i : char :: i in res ==> 0 <= res[i].tid < numberOfThreads
	invariant forall i : char :: i in res ==> res[i].val == 0
	//invariant forall i : char :: i in res ==> res[i].epoch.val in res[i].vc
	//invariant forall i : char :: i in res ==> res[i].vc[res[i].epoch.tid] == res[i].epoch.val
	//invariant forall j : int :: 0 <= i < j ==> res[j].vc[res[j].epoch.tid] >= res[j].vc[j]
	//invariant forall i : char :: i in res ==> res[i].epoch.val == findLargestEpoch(vs,size)
	{
		var c:= vars[j];
		var epoch := Epoch(0,0);
		res := res[c := epoch];
		j := j + 1;
	}
} 

ghost method initThreadMap(numberOfThreads : nat) returns (res : ThreadsMap)
ensures forall i:int :: i in res ==> |res[i]| == numberOfThreads;
ensures forall i: int :: i in res ==> forall j : int :: 0 <= j < numberOfThreads ==> res[i][j] == 0
ensures forall i:int :: i in res <==> 0 <= i < numberOfThreads
ensures |res| == numberOfThreads
{
	var j := 0;
	var tmap : ThreadsMap := map[];
	while( j < numberOfThreads )
	invariant numberOfThreads >= j >= 0  
	invariant forall i:int :: i in tmap ==> |tmap[i]| == numberOfThreads;
	invariant |tmap| == j;
	invariant forall i:int :: i in tmap <==> 0 <= i < j
	invariant forall i : int :: i in tmap ==> forall j : int :: 0 <= j < numberOfThreads ==> tmap[i][j] == 0
	{
		var vc := getEmptyVc(numberOfThreads);
		assert j !in tmap;
        tmap := tmap[j := vc];
		j := j + 1;
	}
	res := tmap;
}



function method getVars(t: Trace, list : seq<char>) : seq<char>
requires |t| >= 0
{
	if(|t| == 0) then list
	else
	match t[0]
	case Write(id, l) => if( l !in list) then getVars(t[1..], [l] + list) else getVars(t[1..], list)  
}

ghost method getEmptyVc ( numberOfThreads : nat ) returns ( res : VC )
requires numberOfThreads > 0
ensures |res| == numberOfThreads
ensures forall i : int :: 0 <= i < numberOfThreads ==> res[i] == 0;
{
			var k := 0;
			res := [];
			while( k < numberOfThreads)
			invariant k == |res|
			invariant numberOfThreads >= k >= 0
			invariant forall i : int :: 0 <= i < k ==> res[i] == 0;
			
			{
				res := [0] + res;
				k := k + 1;
			}
}

ghost method initVarsMap( vars: seq<char>, numberOfThreads : nat) returns (res : VarsMap)
requires |vars| > 0
requires numberOfThreads > 0
requires forall i,j :: 0 <= i < j < |vars| ==> vars[i] != vars[j]
//requires forall i:int :: i in tmap ==> |tmap[i]| == size;
//requires |tmap| == size
//requires forall i:int :: i in tmap <==> 0 <= i < size
//requires forall i :int :: 0 <= i < size ==> forall j : int :: 0 <= j < size ==> tmap[i][j] == 0;
ensures forall i:char :: i in res ==> |res[i]| == numberOfThreads;
ensures forall i:char :: i in res ==> i in vars
//ensures forall i : char :: i in res ==> 0 <= res[i].epoch.tid < size
//ensures forall i : char :: i in res ==> prop_largest_epoch(res[i]) == true
ensures forall i : char :: i in res ==> forall j :int :: 0 <= j < |res[i]| ==> res[i][j] == 0
ensures forall i : char :: i in vars ==> i in res
//ensures forall i : char :: i in res ==> res[i].epoch.val >= 0
//ensures forall i : char :: i in res ==> res[i].epoch.val in res[i].vc
//ensures forall i : char :: i in res ==> res[i].epoch.val == res[i].vc[res[i].epoch.tid]
{
	var j := 0;
	res := map[];
	var i := 0;
	//assume forall i : char :: i in res ==> prop_largest_epoch(res[i]);
	while( j < |vars| )
	//WSWinvariant |res| == j
	invariant 0 <= j <= |vars|
	invariant forall i,j :: 0 <= i < j < |vars| ==> vars[i] != vars[j]
	invariant forall i:char :: i in res ==> |res[i]| == numberOfThreads
	invariant forall i:char :: i in res ==> i in vars
	invariant forall i: int :: 0 <= i < j ==> vars[i] in res
	invariant forall i : char :: i in res ==> i in vars
	//invariant forall i : char :: i in res ==> 0 <= res[i].epoch.tid < size
	//invariant forall i : char :: i in res ==> res[i].epoch.val == 0
	//invariant forall i : char :: i in res ==> size > res[i].epoch.tid >= 0
	invariant forall i : char :: i in res ==> forall j :int :: 0 <= j < |res[i]| ==> res[i][j] == 0
	//invariant forall i : char :: i in res ==> prop_largest_epoch(res[i]) == true
	//invariant forall i : char :: i in res ==> res[i].epoch.val in res[i].vc
	//invariant forall i : char :: i in res ==> res[i].vc[res[i].epoch.tid] == res[i].epoch.val
	//invariant forall j : int :: 0 <= i < j ==> res[j].vc[res[j].epoch.tid] >= res[j].vc[j]
	//invariant forall i : char :: i in res ==> res[i].epoch.val == findLargestEpoch(vs,size)
	{
		var c:= vars[j];
		var vc := getEmptyVc(numberOfThreads);
		res := res[c := vc];
		//assert forall j :int :: 0 <= j < |vc| ==> vc[j] == 0;
		//assert |vc| == size;
		//assert forall i : int :: 0 <= i < |vs.vc| ==> djite.val >= vs.vc[i];
		//assert djite.val == vs.epoch.val;
		//assert djite.tid == 0;
		//assert djite.tid == epoch.tid;
		//assert prop_largest_epoch(vs) == true;
		//res := res[c := vs];
		//assert vs == res[c];
		//assert prop_largest_epoch(res[c]) == true;
		j := j + 1;
	}
} 

ghost method getVarsM(trace: Trace) returns (res: seq<char>)
requires |trace| > 0
ensures |res| > 0
ensures forall i : int :: 0 <= i < |trace| ==> trace[i].loc in res
ensures forall i,j :: 0 <= i < j < |res| ==> res[i] != res[j]
{
	var v := trace[0].loc;
	res := [];
	res := [v] + res;
	var i := 0;
	while( i < |trace| )
	invariant 0 <= i <= |trace|
	invariant forall i,j :: 0 <= i < j < |res| ==> res[i] != res[j]
	invariant forall j : int :: 0 <= j < i ==> trace[j].loc in res 
	invariant |res| > 0
	{
		var step := trace[i];
		if( step.loc !in res) 
		{ 
			res:= [step.loc] + res; 
		}  
		i := i + 1;
	}
}

function getId(t : Op) : Tid
{
	match t
	case Write(id, l) => id
}


function getIds(t : Trace) : seq<Tid>
requires |t| >= 0
{
	if(|t| == 0) then []
	else
	match t[0]
	case Write(id,l) => [id] + getIds(t[1..])
}

ghost method getMaxId(t : Trace) returns ( res : Tid)
requires |t| > 0
ensures forall j : int :: 0 <= j < |t| ==> res >= t[j].tid
ensures exists j : int :: 0 <= j < |t| && res == t[j].tid
{
	var i := 0;
	res := t[0].tid;
	while ( i < |t|)
	invariant 0 <= i <= |t|
	invariant forall j : int :: 0 <= j < i ==> res >= t[j].tid
	invariant exists j : int :: 0 <= j < |t| && res == t[j].tid
	{
		if(t[i].tid > res)
		{
			res := t[i].tid;
		}
		i := i + 1;
	}
}

function getMaxIdF(t : Trace, i : nat, max : int) : Tid
requires |t| > 0
requires |t| >= i >= 0
requires max >= 0
decreases |t| - i
{
	if(i == |t|) then max
	else if (t[i].tid > max) then getMaxIdF(t, i + 1, t[i].tid) else getMaxIdF(t, i + 1, max)
}

