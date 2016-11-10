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

ghost method ftStart(size : nat, vars : seq<char>) returns (res : FtState)
requires size > 0
requires |vars| > 0
requires forall i,j : int :: 0 <= i < j < |vars| ==> vars[i] != vars[j]
ensures forall i:int :: i in res.ts <==> 0 <= i < size
ensures forall j : int :: 0 <= j < size ==> |res.ts[j]| == size
ensures forall j : int :: 0 <= j < size ==> forall i : int :: 0 <= i < size ==> res.ts[j][i] == 0
ensures forall i:char :: i in res.vs ==> i in vars
ensures forall i : char :: i in res.vs ==> 0 <= res.vs[i].tid < size
ensures forall i : char :: i in vars ==> i in res.vs
ensures forall i : int :: 0 <= i < size ==> forall j : int :: 0 <= j < size ==> res.ts[i][j] == 0
ensures forall i : char :: i in res.vs ==> res.vs[i].val == 0
{
	var tmap := initThreadMap(size);
	var emap := initEpochMap(vars,size);
	res := FtState(tmap,emap);
}


ghost method djitStep (ds : DjitState, op : Op, size : nat) returns (res : opt<DjitState>)
requires size > 0
requires op.loc in ds.vs
requires op.tid in ds.ts
requires forall j : int :: j in ds.ts ==> |ds.ts[j]| == size 
requires forall j : char :: j in ds.vs ==> |ds.vs[j]| == size 
requires forall j : int :: j in ds.ts ==> |ds.ts[j]| == size
//ensures (res.Just?) ==> (forall i : int :: 0 <= i < size ==> ds.vs[op.loc][i] <= ds.ts[op.tid][i])
ensures (res.Just?) ==> (forall i : int :: 0 <= i < size ==> ds.vs[op.loc][i] <= ds.ts[op.tid][i])
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
			res :=  Just(ds);
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
requires forall i : char :: i in fs.vs ==> 0 <= fs.vs[i].tid < size
requires forall j : int :: j in fs.ts ==> |fs.ts[j]| == size
requires 0 <= fs.vs[op.loc].tid < size
requires forall i : int :: 0 <= i < |fs.ts[op.tid]| && i != fs.vs[op.loc].tid ==> fs.vs[op.loc].val <= fs.ts[op.tid][i]
//ensures (res.Just?) ==> (forall i : int :: 0 <= i < |fs.ts[op.tid]| ==> fs.vs[op.loc].val <= fs.ts[op.tid][i])
ensures (res.Just?) ==> (forall i : int :: 0 <= i < |fs.ts[op.tid]| ==> fs.vs[op.loc].val <= fs.ts[op.tid][i])
ensures (res == Nothing) ==> (exists i : int :: 0 <= i < size && fs.vs[op.loc].val > fs.ts[op.tid][i]);
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
			res := Just(fs);
		}
	}
}

/*function ftstep_func(fs : FtState, size : nat) : opt<FtState>
{
	ftStep(fs,size)
}
function djitstep_func(ds : FtState, size : nat) : opt<DjitState>
{
	djitStep(ds,size)
} */

lemma ftstep_equals_djitstep(fs : FtState, ds : DjitState, op :  Op, size :nat)
requires size > 0
requires op.loc in fs.vs
requires op.tid in fs.ts
requires forall i : char :: i in fs.vs ==> 0 <= fs.vs[i].tid < size
requires forall j : int :: j in fs.ts ==> |fs.ts[j]| == size
requires forall i : int :: 0 <= i < |fs.ts[op.tid]| && i != fs.vs[op.loc].tid ==> fs.vs[op.loc].val <= fs.ts[op.tid][i]
requires op.loc in ds.vs
requires op.tid in ds.ts
requires forall j : int :: j in ds.ts ==> |ds.ts[j]| == size 
requires forall j : char :: j in ds.vs ==> |ds.vs[j]| == size 
requires forall i : int :: 0 <= i < size ==> fs.ts[op.tid][i] == ds.ts[op.tid][i]
requires forall i : int :: 0 <= i < size ==> ds.vs[op.loc][i] <= fs.vs[op.loc].val
requires (fs.vs[op.loc].val == ds.vs[op.loc][fs.vs[op.loc].tid]);
{
	var ft := ftStep(fs, op, size);
	var djit := djitStep(ds,op,size);
	assert ft.Just? <==> djit.Just?;
	assert ft == Nothing <==> djit == Nothing;
}



/*ghost method ft( trace : Trace, size : nat, vars : seq<char>) returns ( res : bool )
requires |trace| > 0
requires size > 0
requires |vars| > 0
requires forall i,j : int :: 0 <= i < j < |vars| ==> vars[i] != vars[j]
requires forall i : int :: 0 <= i < |trace| ==> 0 <= trace[i].tid < size
requires forall i : int :: 0 <= i < |trace| ==> trace[i].loc in vars
requires forall c : char :: c in vars <==> c in getVars(trace,[])
{
	var fts := ftStart(size,vars);
	var ftres := ftStep(fts,trace[0],size);
	if(ftres.Just?)
	{
		res := false;
	}
	else
	{
		res := true;
	}
	//var c := findLargestEpoch(lmap[vars[0]]);
	//var q := lmap[vars[0]].epoch;
	//assert c.tid == 0;
	//var resft := false;
	//var resdjit := false;
}*/

ghost method djitStart(size : nat, vars : seq<char>) returns (res : DjitState)
requires size > 0
requires |vars| > 0
requires forall i,j : int :: 0 <= i < j < |vars| ==> vars[i] != vars[j]
ensures forall i:int :: i in res.ts <==> 0 <= i < size
ensures forall j : int :: 0 <= j < size ==> |res.ts[j]| == size
ensures forall j : char :: j in res.vs ==> 0 < |res.vs[j]| == size
ensures forall j : int :: 0 <= j < size ==> forall i : int :: 0 <= i < size ==> res.ts[j][i] == 0
ensures forall i:char :: i in res.vs ==> i in vars
ensures forall i : char :: i in vars ==> i in res.vs
ensures forall i : int :: 0 <= i < size ==> forall j : int :: 0 <= j < size ==> res.ts[i][j] == 0
ensures forall i : char :: i in res.vs ==> forall j : int :: 0 <= j < |res.vs[i]| ==> res.vs[i][j] == 0
{
	var tmap := initThreadMap(size);
	var vmap := initVarsMap(vars,size);
	res := DjitState(tmap,vmap);
}

ghost method initEpochMap(vars: seq<char>, size : nat) returns (res : EpochMap)
requires |vars| > 0
requires size > 0
requires forall i,j :: 0 <= i < j < |vars| ==> vars[i] != vars[j]
//requires forall i:int :: i in tmap ==> |tmap[i].vc| == size;
//requires |tmap| == size
//requires forall i:int :: i in tmap <==> 0 <= i < size
//requires forall i :int :: 0 <= i < size ==> forall j : int :: 0 <= j < size ==> tmap[i].vc[j] == 0;
//ensures forall i:char :: i in res ==> |res[i].vc| == size;
ensures forall i:char :: i in res ==> i in vars
ensures forall i : char :: i in res ==> 0 <= res[i].tid < size
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
	invariant forall i : char :: i in res ==> 0 <= res[i].tid < size
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

ghost method initThreadMap(size : nat) returns (res : ThreadsMap)
ensures forall i:int :: i in res ==> |res[i]| == size;
ensures forall i: int :: i in res ==> forall j : int :: 0 <= j < size ==> res[i][j] == 0
ensures forall i:int :: i in res <==> 0 <= i < size
ensures |res| == size
{
	var j := 0;
	var tmap : ThreadsMap := map[];
	while( j < size )
	invariant size >= j >= 0  
	invariant forall i:int :: i in tmap ==> |tmap[i]| == size;
	invariant |tmap| == j;
	invariant forall i:int :: i in tmap <==> 0 <= i < j
	invariant forall i : int :: i in tmap ==> forall j : int :: 0 <= j < size ==> tmap[i][j] == 0
	{
		var vc := getEmptyVc(size);
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

ghost method getEmptyVc ( size : nat ) returns ( res : VC )
requires size > 0
ensures |res| == size
ensures forall i : int :: 0 <= i < size ==> res[i] == 0;
{
			var k := 0;
			res := [];
			while( k < size)
			invariant k == |res|
			invariant size >= k >= 0
			invariant forall i : int :: 0 <= i < k ==> res[i] == 0;
			
			{
				res := [0] + res;
				k := k + 1;
			}
}

ghost method initVarsMap( vars: seq<char>, size : nat) returns (res : VarsMap)
requires |vars| > 0
requires size > 0
requires forall i,j :: 0 <= i < j < |vars| ==> vars[i] != vars[j]
//requires forall i:int :: i in tmap ==> |tmap[i]| == size;
//requires |tmap| == size
//requires forall i:int :: i in tmap <==> 0 <= i < size
//requires forall i :int :: 0 <= i < size ==> forall j : int :: 0 <= j < size ==> tmap[i][j] == 0;
ensures forall i:char :: i in res ==> |res[i]| == size;
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
	invariant forall i:char :: i in res ==> |res[i]| == size
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
		var vc := getEmptyVc(size);
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

