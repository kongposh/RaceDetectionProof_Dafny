datatype Op = Write(tid:int, loc: int)
datatype opt<T> = Just(value: T) | Nothing
datatype FtState = FtState(ts : ThreadsMap, vs: EpochMap, ls : VarsMap)
datatype DjitState = DjitState(ts : ThreadsMap, vs: VarsMap, ls : VarsMap)
datatype Epoch = Epoch(tid : int, val : int)
type ThreadsMap = map<int, VC>
type VarsMap = map<int, VC>
type EpochMap = map<int, Epoch>
type Trace = seq<Op>
type VC = map<int,int>

//The initial state of the fast track algorithm which returns an
//empty map for each map in the state.
function ftStart() : FtState
ensures (wellFormed(ftStart()))
{
	var tmap := map[];
	var emap := map[];
	var lmap := map[];
	FtState(tmap,emap,lmap)
}


predicate wellFormed(res : FtState) {
 //forall i :: i in res.ts ==> i in res.ts[i] && forall c : char :: c in res.vs && 
// forall loc : int :: loc in res.vs && res.vs[c].tid in res.ts && res.vs[c].tid in res.ts[res.vs[c].tid] ==> ( res.vs[c].val <= res.ts[res.vs[c].tid][res.vs[c].tid] ) 
 (forall loc : int :: loc in res.vs ==> res.vs[loc].val <= lookupVC(lookup(res.ts, res.vs[loc].tid), res.vs[loc].tid)) 
// && (forall tid1 , tid2 : int :: tid1 in res.ts ==> lookupVC( lookup(res.ts, tid1) , tid1) >= lookupVC( lookup(res.ts, tid2) , tid1)) 
 //forall loc : int :: lookupEpoch(res.vs, loc).val <= lookupVC(lookup(res.ts, lookupEpoch(res.vs, loc).tid), lookupEpoch(res.vs, loc).tid)
 }

function addThread(tmap: ThreadsMap, tid:int) : ThreadsMap 
{ 
	tmap[tid := map[tid := 0]]
}

function lookup(m:map<int, VC>, i:int) : VC
{
	if(i in m) then m[i] else map[]
}

function lookupVC(vc:VC, tid:int) : int
{
	if(tid in vc) then vc[tid] else 0
}

function lookupEpoch(m:map<int, Epoch>, i:int) : Epoch
{
	if(i in m) then m[i] else Epoch(i,0)
}


function incrementVC(vc:VC, threadID:int) : VC
//ensures forall tid:int :: tid in vc ==> tid in incrementVC(vc, threadID)
//ensures forall tid:int :: tid in vc ==> vc[tid] <= incrementVC(vc, threadID)[tid]
{
	if(threadID in vc)
		then vc[threadID := vc[threadID]+1]
		else vc[threadID :=  1]
}

function updateEpoch(threadID:int, threadVC:VC) : Epoch
{
	Epoch(threadID, lookupVC(threadVC, threadID))
}

function updateLocVC(threadID:int, threadVC:VC, locVC:VC) : VC
{
	locVC[threadID := lookupVC(threadVC, threadID)]
}


lemma proof(fs : FtState, ds : DjitState, op : Op)
requires wellFormed(fs)
requires wellFormedDjit(ds)
ensures (ftStep(fs,op).Just? && djitStep(ds,op).Just?) ==> wellFormed(ftStep(fs,op).value) == wellFormedDjit(djitStep(ds,op).value);
{

}


function ftStep(fs : FtState, op : Op) : opt<FtState>
requires(wellFormed(fs))
ensures (var res:= ftStep(fs,op); ftStep(fs,op).Just? ==> wellFormed(res.value))
{
	//assert lookupVC(lookup(fs.ts, lookupEpoch(fs.vs,op.loc).tid),lookupEpoch(fs.vs,op.loc).tid) >= lookupEpoch(fs.vs,op.loc).val; 
	match op
	case Write(tid, loc) =>
		var threadVC := lookup(fs.ts, tid);
		var locEpoch := lookupEpoch(fs.vs, loc);
		var threadVC' := incrementVC(threadVC, tid);
		var locEpoch' := updateEpoch(tid, threadVC);
		if(lookupVC(threadVC', locEpoch.tid) < locEpoch.val) then Nothing
		else
			Just(FtState(fs.ts[tid := threadVC'], fs.vs[loc := locEpoch'], fs.ls))
}

function djitStart() : DjitState
ensures wellFormedDjit(djitStart())
{
	var tmap := map[];
	var vmap := map[];
	var lmap := map[];
	DjitState(tmap,vmap,lmap)
}

predicate wellFormedDjit(ds : DjitState) 
{
	forall i: int :: i in ds.vs ==> forall j : int :: j in lookup(ds.vs,i) ==> lookupVC(lookup(ds.ts,j),j) >= lookupVC(lookup(ds.vs,i),j)                     //lookupVC(lookup(ds.ts,j),j) >= lookupVC(lookup(ds.vs,i),j)
}

function djitStep(ds : DjitState, op : Op) : opt<DjitState>
requires(wellFormedDjit(ds))
ensures (var res:= djitStep(ds,op); djitStep(ds,op).Just? ==> wellFormedDjit(res.value))
{
	match op
	case Write(tid, loc) =>
		var threadVC := lookup(ds.ts, tid);
		var locVC := lookup(ds.vs, loc);
		var threadVC' := incrementVC(threadVC, tid);
		var locVC' := updateLocVC(tid, threadVC',locVC);
		if(vcleq(threadVC, locVC)) then 
			Just(DjitState(ds.ts[tid := threadVC'],ds.vs[loc := locVC'], ds.ls))
		else 
			Nothing
}

predicate vcleq ( threadVC : VC, locVC : VC)
{
	forall i : int :: i in locVC ==> lookupVC(threadVC, i) >= lookupVC(locVC, i)
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

/*
requires forall i :: i in fs.ts ==> i in fs.ts[i]
requires forall c :: c in fs.vs ==> fs.vs[c].tid in fs.ts
requires (forall c : char :: c in fs.vs ==> fs.vs[c].val <= fs.ts[fs.vs[c].tid][fs.vs[c].tid])
//requires op.tid in fs.ts ==> op.tid in fs.ts[op.tid]
requires (op.loc in fs.vs && op.tid in fs.ts && fs.vs[op.loc].tid in fs.ts[op.tid] ==> var eid := fs.vs[op.loc].tid; var eval := fs.vs[op.loc].val; eval < fs.ts[op.tid][eid])
ensures (var res:= ftStep(fs,op); res.Just? ==> res.value.vs[op.loc].val <= res.value.ts[op.tid][res.value.vs[op.loc].tid])
//ensures (var res:= ftStep(fs,op); res.Just? ==> forall i :: i in res.value.ts ==> i in res.value.ts[i])
//ensures (var res:= ftStep(fs,op); res.Just? ==> op.tid in fs.ts ==> op.tid in fs.ts[op.tid])
//ensures (var res := ftStep(fs,op); res.Just? ==> forall c : char :: c in res.value.vs && res.value.vs[c].tid in res.value.ts ==> res.value.vs[c].val <= res.value.ts[res.value.vs[c].tid][res.value.vs[c].tid] )

*/

