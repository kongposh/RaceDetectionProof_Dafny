datatype Op = Write(tid:Tid, loc: Var)
datatype ThreadState = ThreadState(tid:Tid, vc:VC)
datatype VarState = VarState(Var,epoch:Epoch, vc:VC)
datatype Epoch = Epoch(tid : Tid, val : Value)
type Tid = int
type Value = int

type Var = char
type Trace = seq<Op>
type VC = seq<int>
type ThreadsMap = map<Tid, ThreadState>
type VarsMap = map<Var, VarState>

/* ghost method race(trace : Trace, size : nat, vars : seq<char>) returns (res : bool)
requires |trace| > 0
requires size > 0
requires |vars| > 0
requires forall i,j : int :: 0 <= i < j < |vars| ==> vars[i] != vars[j]
requires forall i : int :: 0 <= i < |trace| ==> 0 <= trace[i].tid < size
requires forall i : int :: 0 <= i < |trace| ==> trace[i].loc in vars
requires forall c : char :: c in vars <==> c in getVars(trace,[])
ensures res == true
{
	var t :=  findRace(trace,size,vars);
	var t2 := findRaceFT(trace,size,vars);
	return t == t2;
} */

/*ghost method findRace(trace : Trace, size : nat, vars : seq<char>) returns ( res : bool)
requires |trace| > 0
requires size > 0
requires |vars| > 0
requires forall i,j : int :: 0 <= i < j < |vars| ==> vars[i] != vars[j]
requires forall i : int :: 0 <= i < |trace| ==> 0 <= trace[i].tid < size
requires forall i : int :: 0 <= i < |trace| ==> trace[i].loc in vars
requires forall c : char :: c in vars <==> c in getVars(trace,[])
{
	var tmap := initThreadVC(size);
	var lmap := initVarVCW(vars,size);
	assert forall i:char :: i in vars ==> i in lmap;
	assert forall i:int :: 0 <= i < |trace| ==> trace[i].loc in lmap;
	var i := 0;
	res := false;
	while( i < |trace|)
	invariant forall i:char :: i in lmap ==> |lmap[i].vc| == size;
	invariant forall i:char :: i in lmap ==> i in vars;
	invariant forall i: char :: i in lmap ==> prop_largest_epoch(lmap[i]) == true
	{
	var op := trace[i];
	match op
	case Write(tid, loc) => {
	var ts := tmap[tid];
	var vs := lmap[loc];
	var e := findLargestEpoch(vs,size);
	assert forall i : int :: 0 <= i < size ==> e.val >= vs.vc[i];
	if ( e.val > ts.vc[e.tid])
	{
		res := true;
	}
	} 
	i := i + 1;
	}
	
} */

/*function findRaceStep( op : Op , tmap : ThreadsMap, lmap : VarsMap) : bool
requires forall i:char :: i in lmap ==> |lmap[i].vc| == size;
requires forall i:char :: i in lmap ==> i in vars;
requires forall i: char :: i in lmap ==> prop_largest_epoch(lmap[i]) == true
//ensures findRaceStep(op,tmap,lmap) == false ==> forall i: char :: i in lmap ==> prop_largest_epoch(lmap[i]) == true
{
	match op
	case Write(tid, loc) =>
	var ts := tmap[tid];
	var vs := lmap[loc];
	var e := findLargestEpoch(vs,size);
	assert forall i : int :: 0 <= i < size ==> e.val >= vs.vc[i];
	if ( e.val > ts.vc[e.tid]) then true
	else false
}*/

/*ghost method djitChecker(ts : ThreadState, vs : VarState) returns (res : bool)
requires |vs.vc| == |ts.vc|;
requires 0 <= vs.epoch.tid < |vs.vc|
requires vs.vc[vs.epoch.tid] == vs.epoch.val
requires forall i : int :: 0 <= i < |vs.vc| ==> vs.vc[i] >= 0
requires 0 <= vs.epoch.val
requires vs.epoch.val in vs.vc
ensures res == true ==> exists i : int :: 0 <= i < |vs.vc| ==> vs.vc[i] < ts.vc[i]
{
	var i := 0;
	res := false;
	while ( i < |vs.vc|)
	{
		var t := ts.vc[i];
		var v := vs.vc[i];
		if(v > t)
		{
			res := true; 
		}
		i := i + 1;
	}

} */

ghost method ftChecker(ts : ThreadState, vs: VarState) returns (res : bool)
requires |vs.vc| == |ts.vc|;
requires 0 <= vs.epoch.tid < |vs.vc|
requires vs.epoch.val == vs.vc[vs.epoch.tid];
requires prop_largest_epoch(vs) == true
requires vs.epoch.val in vs.vc
requires forall i : int :: 0 <= i < |vs.vc| ==> vs.vc[i] <= ts.vc[i];
//ensures res == true ==> vs.epoch.val - ts.vc[vs.epoch.tid] > 0
ensures res == true ==> exists i : int :: 0 <= i < |vs.vc| && vs.vc[i] > ts.vc[i];
//ensures res == false ==> forall i : int :: 0 <= i < |vs.vc| ==> vs.vc[i] <= ts.vc[i];
{
	var e := vs.epoch;
	if ( e.val > ts.vc[e.tid])
	{
		res := true;
		assert exists i : int :: 0 <= i < |ts.vc| && vs.vc[i] > ts.vc[i];
		//assert e.val > ts.vc[e.tid];
		//assert e.val == vs.vc[e.tid];
		//assert vs.vc[e.tid] > ts.vc[e.tid];
		// Info: epoch value is greater than some corresponding ts [epoch.id]
		// There exist many values in vs where epoch.val >= vs.vc[i]
		// Since epoch.tid is in these values, one of these indices should have a corresponding vs value greater


		//assert ((exists i : int :: 0 <= i < |ts.vc| && e.val > ts.vc[i]) && ( forall i : int :: 0 <= i < |ts.vc| ==> e.val >= vs.vc[i])) ==> (exists i :int :: 0 <= i < |ts.vc| && vs.vc[i] > ts.vc[i]);
		//assert forall i : int :: 0 <= i < |vs.vc| ==> e.val >= vs.vc[i];
		
	}
	else
	{
		res := false;
	}
	
	//assert exists i : int :: 0 <= i < |vs.vc| ==> vs.vc[i] <= ts.vc[i];
}

ghost method findRaceFT(trace : Trace, size : nat, vars : seq<char>, ftmode: bool) returns ( res : bool)
requires |trace| > 0
requires size > 0
requires |vars| > 0
requires forall i,j : int :: 0 <= i < j < |vars| ==> vars[i] != vars[j]
requires forall i : int :: 0 <= i < |trace| ==> 0 <= trace[i].tid < size
requires forall i : int :: 0 <= i < |trace| ==> trace[i].loc in vars
requires forall c : char :: c in vars <==> c in getVars(trace,[])
//ensures var ft := findRaceFT(trace, size, vars, true); var djit := findRaceFT(trace, size, vars, false); ft==djit;
{

	var tmap := initThreadVC(size);
	var lmap := initVarVCW(vars,size,tmap);
	var c := findLargestEpoch(lmap[vars[0]]);
	var q := lmap[vars[0]].epoch;
	assert c.tid == 0;
	var resft := false;
	var resdjit := false;

	var i := 0;
	res := false;
	while( i < |trace|)
	invariant forall i:char :: i in lmap ==> |lmap[i].vc| == size;
	invariant forall i:char :: i in lmap ==> i in vars;
	invariant forall i:int :: i in tmap ==> 0 <= |tmap[i].vc| == size;
	invariant forall i:char :: i in lmap ==> 0 <= lmap[i].epoch.tid < size
	invariant forall i: char :: i in lmap ==> prop_largest_epoch(lmap[i]) == true
	invariant resft == resdjit
	invariant forall i : int :: 0 <= i < size ==> i in tmap
	{
	var op := trace[i];
	match op
	case Write(tid, loc) => {
	var ts := tmap[tid];
	var vs := lmap[loc];
	var e := vs.epoch;
	assume forall i : int :: 0 <= i < |vs.vc| ==> vs.vc[i] <= ts.vc[i];
	resft := ftChecker(ts,vs);
	resdjit := djitChecker(ts,vs);
	assert resft == resdjit;

	if(resft == true)
	{
		res := true;
		return res;
	}
	else
	{
		//update ts
		var tsv := ts.vc[tid];
		tsv := tsv + 1;
		var vct := ts.vc;
		vct := vct[tid := tsv];
		var tst := ThreadState(i, vct);
		tmap := tmap[tid := tst];

		//update vs
		var vsv := vs.vc[tid];
		vsv := vsv + 1;
		var vsvct := vs.vc;
		vsvct := vsvct[tid := vsv];
		var et := Epoch(tid,vs.vc[tid]);
		var vst := VarState(loc, et,vsvct);
	}
	//checkWriteDJIT
	
	//assert checkWriteFT(...) == checkWriteDJIT(...)

	//var c := findLargestEpoch(vs);
	assert forall i : int :: 0 <= i < |vs.vc| ==> e.val - vs.vc[i] >= 0;
	//forall values in the vector clock of the variable written the epoch is equal or larger
	//ft only checks if the epoch is greater to return an error
	//djit checks if any are greater to return an error
	assert e.val == c.val;
	//assert e.tid == c.tid;
	} 
	i := i + 1;
	}
} 

/*function findLargestEpochFunc(vs : VarState, size : nat) :  Epoch
requires |vs.vc| == size
requires 0 <= vs.epoch.tid < size
requires forall i : int :: 0 <= i < |vs.vc| ==> vs.vc[i] >= 0
requires 0 <= vs.epoch.val
//ensures forall i : int :: 0 <= i < |vs.vc| ==> findLargestEpochFunc(vs,size).val >= vs.vc[i]
//ensures 0 <= findLargestEpochFunc(vs,size).tid < size
{
	findLargestEpochFromVc(vs.vc, Epoch(0,0), 0)
}

function findLargestEpochFromVc(vc : VC,  e : Epoch, i : nat) : Epoch
requires |vc| >= i >= 0
ensures forall j : int :: 0 <= j < i ==> findLargestEpochFromVc(vc[0..j],Epoch(0,vc[0]),0).val >= vc[j]
//ensures forall i,j : int :: 0 <= i < j <= |vc| ==> findLargestEpochFromVc(vc[0..j],Epoch(0,vc[0]),0).val >= vc[i]
decreases |vc| - i
{
	if(i == |vc|) then e
	else if(vc[i] >= e.val) then findLargestEpochFromVc(vc, Epoch(i,vc[i]), i + 1) else findLargestEpochFromVc(vc, e, i + 1)
}*/

/*function prop_same_largest(vs : VarState) : bool
requires 0 <= vs.epoch.tid < |vs.vc|
requires vs.vc[vs.epoch.tid] == vs.epoch.val
requires forall i : int :: 0 <= i < |vs.vc| ==> vs.vc[i] >= 0
requires 0 <= vs.epoch.val
requires forall i : int :: 0 <= i < |vs.vc| ==> vs.epoch.val >= vs.vc[i]
requires 0 <= vs.epoch.tid < |vs.vc|
requires forall j : int :: 0 <= j < |vs.vc| ==> vs.vc[vs.epoch.tid] >= vs.vc[j]
requires vs.vc[vs.epoch.tid] == vs.epoch.val
requires vs.epoch.val in vs.vc
{
	var e := vs.epoch;
	var c := findLargestEpoch(vs);
	e.val == c.val
}*/

ghost method djitChecker ( ts : ThreadState, vs : VarState) returns ( res : bool)
requires |vs.vc| == |ts.vc|;
requires 0 <= vs.epoch.tid < |vs.vc|
requires vs.epoch.val == vs.vc[vs.epoch.tid];
requires vs.epoch.val in vs.vc
ensures res == true ==> exists i : int :: 0 <= i < |vs.vc| && vs.vc[i] > ts.vc[i];
{
	res := false;
	var i := 0;
	while ( i < |ts.vc|)
	invariant 0 <= i <= |ts.vc|
	invariant res == true ==> exists j : int :: 0 <= j < i && vs.vc[j] > ts.vc[j];
	{
	var t := ts.vc[i];
	var e := vs.vc[i];
	if( e > t )
	{
		res := true;
		assert exists j : int :: 0 <= j < i ==> vs.vc[j] > ts.vc[j];
	}
	i := i + 1;
	}
	assert res == true ==> exists j : int :: 0 <= j < |vs.vc| ==> vs.vc[j] > ts.vc[j];
	
}

ghost method findLargestEpoch(vs : VarState) returns ( res : Epoch)
requires 0 <= vs.epoch.tid < |vs.vc|
requires vs.vc[vs.epoch.tid] == vs.epoch.val
ensures 0 <= res.tid < |vs.vc|
ensures forall j : int :: 0 <= j < |vs.vc| ==> vs.vc[res.tid] >= vs.vc[j]
ensures vs.vc[res.tid] == res.val
requires forall i : int :: 0 <= i < |vs.vc| ==> vs.vc[i] >= 0
requires 0 <= vs.epoch.val
requires vs.epoch.val in vs.vc
ensures forall i : int :: 0 <= i < |vs.vc| ==> res.val >= vs.vc[i]
ensures res.val in vs.vc
ensures 0 <= res.tid < |vs.vc|
ensures (forall j : int :: 0 <= j < |vs.vc| ==> vs.vc[j] == 0) ==> res.tid == 0
{
	var i := 0;
	//var e := vs.vc[0];
	res := Epoch(0,vs.vc[0]);
	var vc := vs.vc;
	while( i < |vc|)
	invariant 0 <= i <= |vc|
	invariant forall j : int :: 0 <= j < i ==> res.val >= vc[j]
	invariant 0 <= res.tid < |vs.vc|
	invariant res.val in vs.vc
	invariant vs.vc[res.tid] == res.val
	invariant forall j : int :: 0 <= j < i ==> vc[res.tid] >= vc[j]
	invariant (forall j : int :: 0 <= j < i ==> vc[j] == 0) ==> res.tid == 0
	{
		var v := vc[i];
		if(v > res.val)
		{
			res := Epoch(i,v);
		}
		i := i + 1;
	}
	assert forall j : int :: 0 <= j < |vs.vc| ==> res.val >= vs.vc[j];
}

function method getVars(t: Trace, list : seq<char>) : seq<char>
requires |t| >= 0
{
	if(|t| == 0) then list
	else
	match t[0]
	case Write(id, l) => if( l !in list) then getVars(t[1..], [l] + list) else getVars(t[1..], list)  
}

method getVarsM(trace: Trace) returns (res: seq<char>)
requires |trace| > 0
ensures |res| > 0
ensures forall i,j :: 0 <= i < j < |res| ==> res[i] != res[j]
{
	var v := trace[0].loc;
	res := [];
	res := [v] + res;
	var i := 0;
	while( i < |trace| )
	invariant 0 <= i <= |trace|
	invariant forall i,j :: 0 <= i < j < |res| ==> res[i] != res[j]
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


function getVar(t : Op) : char
{
	match t
	case Write(id, l) => l


}


ghost method initThreadVC(size : nat) returns (res : ThreadsMap)
ensures forall i:int :: i in res ==> |res[i].vc| == size;
ensures forall i: int :: i in res ==> forall j : int :: 0 <= j < size ==> res[i].vc[j] == 0
ensures forall i:int :: i in res <==> 0 <= i < size
ensures |res| == size
{
	var j := 0;
	var tmap : ThreadsMap := map[];
	while( j < size )
	invariant size >= j >= 0
	//invariant forall k :: 0 <= k < j ==> k in tmap  
	invariant forall i:int :: i in tmap ==> |tmap[i].vc| == size;
	invariant |tmap| == j;
	invariant forall i:int :: i in tmap <==> 0 <= i < j
	invariant forall i : int :: i in tmap ==> forall j : int :: 0 <= j < size ==> tmap[i].vc[j] == 0
	{
		var vc := getEmptyVc(size);
		var tid := j;
		var epoch := Epoch(j,vc[j]);
		var ts := ThreadState(j,vc);
        tmap := tmap[j := ts];
		j := j + 1;
	}
	res := tmap;
}

ghost method initVarVCW( vars: seq<char>, size : nat, tmap : ThreadsMap) returns (res : VarsMap)
requires |vars| > 0
requires size > 0
requires forall i,j :: 0 <= i < j < |vars| ==> vars[i] != vars[j]
requires forall i:int :: i in tmap ==> |tmap[i].vc| == size;
requires |tmap| == size
requires forall i:int :: i in tmap <==> 0 <= i < size
requires forall i :int :: 0 <= i < size ==> forall j : int :: 0 <= j < size ==> tmap[i].vc[j] == 0;
ensures forall i:char :: i in res ==> |res[i].vc| == size;
ensures forall i:char :: i in res ==> i in vars
ensures forall i : char :: i in res ==> 0 <= res[i].epoch.tid < size
ensures forall i : char :: i in res ==> prop_largest_epoch(res[i]) == true
ensures forall i : char :: i in res ==> forall j :int :: 0 <= j < |res[i].vc| ==> res[i].vc[j] == 0
ensures forall i : char :: i in vars ==> i in res
ensures forall i : char :: i in res ==> res[i].epoch.val >= 0
ensures forall i : char :: i in res ==> res[i].epoch.val in res[i].vc
ensures forall i : char :: i in res ==> res[i].epoch.val == res[i].vc[res[i].epoch.tid]
{
	var j := 0;
	res := map[];
	/*var c := vars[0];
	var vc := getEmptyVc(size);
	var epoch := Epoch(0,0);
	assert forall i : int :: 0 <= i < |vc| ==> epoch.val >= vc[i];
	var vs := VarState(c,epoch,vc);
	res := map [];
    res := res[c := vs];
	assert c in vars;
	assert c in res;
	assert |res| == 1;	
	assert prop_largest_epoch(vs) == true;*/
	var i := 0;
	assume forall i : char :: i in res ==> prop_largest_epoch(res[i]);
	while( j < |vars| )
	//WSWinvariant |res| == j
	invariant 0 <= j <= |vars|
	invariant forall i,j :: 0 <= i < j < |vars| ==> vars[i] != vars[j]
	invariant forall i:char :: i in res ==> |res[i].vc| == size
	invariant forall i:char :: i in res ==> i in vars
	invariant forall i: int :: 0 <= i < j ==> vars[i] in res
	invariant forall i : char :: i in res ==> i in vars
	invariant forall i : char :: i in res ==> 0 <= res[i].epoch.tid < size
	invariant forall i : char :: i in res ==> res[i].epoch.val == 0
	invariant forall i : char :: i in res ==> size > res[i].epoch.tid >= 0
	invariant forall i : char :: i in res ==> forall j :int :: 0 <= j < |res[i].vc| ==> res[i].vc[j] == 0
	invariant forall i : char :: i in res ==> prop_largest_epoch(res[i]) == true
	invariant forall i : char :: i in res ==> res[i].epoch.val in res[i].vc
	invariant forall i : char :: i in res ==> res[i].vc[res[i].epoch.tid] == res[i].epoch.val
	//invariant forall j : int :: 0 <= i < j ==> res[j].vc[res[j].epoch.tid] >= res[j].vc[j]
	//invariant forall i : char :: i in res ==> res[i].epoch.val == findLargestEpoch(vs,size)
	{
		var c:= vars[j];
		var vc := getEmptyVc(size);
		var epoch := Epoch(0,vc[0]);
		var vs := VarState(c,epoch,vc);

		assert forall j :int :: 0 <= j < |vs.vc| ==> vs.vc[j] == 0;
		assert vs.epoch.val == 0;
		assert size > 0;
		assert vs.epoch.tid == 0 ;
		assert |vs.vc| == size;
		assert epoch.val in vs.vc;
		assert forall i : int :: 0 <= i < |vc| ==> epoch.val >= vc[i];
		assert epoch.tid == 0;
		var djite := findLargestEpoch(vs);
		assert forall i : int :: 0 <= i < |vs.vc| ==> djite.val >= vs.vc[i];
		assert djite.val == vs.epoch.val;
		assert djite.tid == 0;
		assert djite.tid == epoch.tid;
		assert prop_largest_epoch(vs) == true;
		res := res[c := vs];
		assert vs == res[c];
		assert prop_largest_epoch(res[c]) == true;
		j := j + 1;
	}

	
} 


function prop_largest_epoch(vs : VarState) : bool
{
	forall i:int :: 0 <= i < |vs.vc| ==> vs.epoch.val >= vs.vc[i]  	
}

ghost method getEmptyVc ( size : nat ) returns ( res : VC )
requires size > 0
ensures |res| == size
ensures forall i : int :: 0 <= i < size ==> res[i] == 0;
{
			var k := 0;
			res := [];
			//var vc : VC := [];
			while( k < size)
			invariant k == |res|
			invariant size >= k >= 0
			invariant forall i : int :: 0 <= i < k ==> res[i] == 0;
			
			{
				res := [0] + res;
				k := k + 1;
			}
}



