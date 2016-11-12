datatype Op = Write(tid:int, loc: char)
datatype opt<T> = Just(value: T) | Nothing
datatype FtState = FtState(ts : ThreadsMap, vs: EpochMap, ls : VarsMap)
datatype DjitState = DjitState(ts : ThreadsMap, vs: VarsMap)
datatype Epoch = Epoch(tid : int, val : int)
type ThreadsMap = map<int, VC>
type VarsMap = map<char, VC>
type EpochMap = map<char, Epoch>
type Trace = seq<Op>
type VC = map<int,int>

//The initial state of the fast track algorithm which returns an
//empty map for each map in the state.
/*function ftStart(numberOfThreads : nat) : FtState
requires numberOfThreads > 0
{
	var tmap := createThreadsMap(numberOfThreads);
	assert |tmap| == numberOfThreads;
	assert forall t : int :: t in tmap ==> |tmap[t]| == numberOfThreads;
	assert forall t,u : int :: t in tmap && u in tmap && u != t ==> tmap[u][t] < tmap[t][t];
	var emap := map[];
	var lmap := map[];
	//assert 3 == 4;
	FtState(tmap,emap, lmap)
}

function createThreadsMap(numberOfThreads : nat) : ThreadsMap
//ensures forall t : int :: t in createThreadsMap(numberOfThreads) ==> |createThreadsMap(numberOfThreads)[t]| == numberOfThreads
//ensures |createThreadsMap(numberOfThreads)| == numberOfThreads
{
	var v := initThreadMap(numberOfThreads,numberOfThreads);
	//assert |v| == 3;
	//assert v[1][1] == v[0][0];
	assert forall t,u : int :: t in v && u in v && u != t ==> v[u][t] < v[t][t];
	v
}

function method initThreadMap(numberOfThreads : nat, const_numberOfThreads : nat) : ThreadsMap
requires const_numberOfThreads >= numberOfThreads >=0
ensures forall t : int :: t in initThreadMap(numberOfThreads,const_numberOfThreads) ==> 0 <= t < numberOfThreads
ensures |initThreadMap(numberOfThreads, const_numberOfThreads)| == numberOfThreads
ensures forall t : int :: t in initThreadMap(numberOfThreads,const_numberOfThreads) ==> |initThreadMap(numberOfThreads,const_numberOfThreads)[t]| == const_numberOfThreads;
ensures (var tmap := initThreadMap(numberOfThreads,const_numberOfThreads); forall t : int :: t in tmap ==> tmap[t][t] == 1);
{
	if( numberOfThreads == 0) then map[]
	else var tempMap := initThreadMap(numberOfThreads-1,const_numberOfThreads); tempMap[numberOfThreads-1 := getEmptyVC(numberOfThreads-1,const_numberOfThreads)]
}

function method getEmptyVC( currId : nat , numberOfThreads : nat) : seq<int>
requires 0 <= currId 
ensures |getEmptyVC(currId,numberOfThreads)| == numberOfThreads
ensures (var m := getEmptyVC(currId,numberOfThreads); |m| >= currId ==> m[currId] == 1)
{
	if(numberOfThreads == 0) then []
	else if(currId == numberOfThreads - 1) then getEmptyVC(currId,numberOfThreads-1)+[1]
	else getEmptyVC(currId, numberOfThreads-1)+[0]
}*/

function ftStep(fs : FtState, op : Op) : opt<FtState>
requires forall t,u : int :: t in fs.ts && u in fs.ts && u != t ==> fs.ts[u][t] < fs.ts[t][t]
{
	match op
	case Write(tid, loc) => if(tid !in fs.ts && loc !in fs.vs) then Just(FtState(map[tid := map[tid := 1]], map[loc := Epoch(tid,0)],fs.ls)) 
	else if (tid !in fs.ts) then Nothing
	else if (tid in fs.ts && loc !in fs.vs) then var oldVal := fs.ts[tid][tid];  
	
	
	//update ts
	var tmap := fs.ts;
	var tvc := tmap[tid]; 
	var tval := tvc[tid] + 1;
	var tvc := tvc[tid := tval];
	var tmap := tmap [ tid := tvc];
	Just(FtState(tmap,map[loc := Epoch(tid,0)],fs.ls))
	else Nothing	
	//var eid := if(tid !in fs.ts) then           //fs.vs[loc].tid; 
	//if(fs.vs[loc].val > fs.ts[tid][eid]) then Nothing else Just(fs)
} 



/*ghost method getEmptyVc ( numberOfThreads : nat ) returns ( res : VC )
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
}*/
/*ghost method initThreadMap(numberOfThreads : nat) returns (res : ThreadsMap)
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
        tmap := tmap[j := vc];
		j := j + 1;
	}
	res := tmap;
}*/








function getMaxIdF(t : Trace) : int
{
	if(|t| == 0) then 0
	else 1
	//else max(t[0].tid, getMaxIdF(t[1..])) 
}

