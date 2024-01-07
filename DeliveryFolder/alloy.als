open util/relation
open util/boolean


sig Tournament {}


sig Battle {
	belongsTo: one Tournament
}


sig Student {}


sig Score in Int {}


sig Submission {
	group: one Group,
	score: one Score,
	var submited: one Bool
}{ score>=0 and score<=100 }


sig Group {
	participants: set Student,
	battle: Battle
} { participants !=none and cannotEnrollTwiceInABattle }

pred cannotEnrollTwiceInABattle {
	all disj g,h:Group | g.participants&h.participants=none or g.battle!=h.battle
}





fun submissions [g:Group]:set Submission{
	(group:>g).dom
}

fun effectiveSubmissions [g:Group]:set Submission{
	{s:g.submissions | s.submited.isTrue}
}

fun scores [g:Group]: set Score{
	g.effectiveSubmissions.score
}

fun bestScore [g:Group]: Score {
	max[g.scores + {0}]
}

fun participants[t:Tournament]:Student {
	{s:Student | (some g:Group | t=g.battle.belongsTo and s in g.participants)}
}

fun groupsForATournament[s:Student, t:Tournament]: set Group {
	{g:Group | s in g.participants and t=g.battle.belongsTo }
}

fun scoreInTournament[s:Student, t:Tournament]: Int{
	sum g:s.groupsForATournament[t] | g.bestScore
}


fun ranking[t:Tournament]: Student -> Student {
	{b,w: t.participants | int b.scoreInTournament[t]>= int w.scoreInTournament[t]}
}




fact noSubmissionsAtStart {
		all s:Submission| s.submited.isFalse
}

pred allTournamentsEnd {
	eventually all s:Submission| s.submited.isTrue
}

fact {allTournamentsEnd}

pred submit [s:Submission]{
	submited' = submited ++ s->True
}

fact oneSubmissionPerStep {
	always some s:Submission| s.submit
}

/*
//A simple example with two submissions to see if the behavior is the expected one.
run {} for 5 but exactly 2 Submission, 9 int

//An example where the final ranking is a relation of total order (i.e. with no ties and everyone participates)
run {
	eventually some t:Tournament |  totalOrder[t.ranking,Student] 
} for 3 but exactly 1 Tournament, exactly 3 Student, 9 int


//Counterexample to prove that ranking is not always a partial order (neither a total order)  because of ties
check {
	after  all t:Tournament | partialOrder[t.ranking,t.participants]
}  for 9 Int


//Lets check that it is indeed a preorder
check {
	after all  t:Tournament |  preorder[t.ranking,t.participants]
} for 9 Int
*/
//Simple example to show that a student can improve his score and tie the best one
//Because the relation has only 2 participants: the ranking relation is symmetric iff there is a tie
run {
	eventually some  t:Tournament | #t.participants=2 and symmetric[t.ranking];
	some  t:Tournament | antisymmetric[t.ranking];
	some  t:Tournament | symmetric[t.ranking]
} for 3 but exactly 2 Student, 1 Tournament, 9 int
