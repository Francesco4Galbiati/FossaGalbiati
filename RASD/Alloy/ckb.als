//Abstract signature for users
abstract sig User {
u_id : one Int,
email : one String
}

//Used to represent an instance of time, for simplicity is limited to date, but it could be extended to DateTime
sig Date{
	year: one Int,
	month: one Int,
	day: one Int
}

//Educators are the users that can create and manage battles and tournaments
sig Educator extends User{
	battlesCreated: set Battle,
	tournamentsCreated: set Tournament,
	tournamentsManaged: set Tournament
}

//Students can participate in tournaments and in battles through teams
sig Student extends User{
	tournaments: set Tournament,
	battles: set Battle,
	teams: set Team
	
}


//Battles have some parameters that need to be inserted by the creator, these parameters must respect the following constraints:
//	- The number of minimum students per team must be less or equal than the maximum number of students (and it should be greateo or equal than 1)
//  - The registration deadline must be before the submission one
//In the signature are also specified the scoring parameters and the test cases and //?
sig Battle{
	name: one String,
	maxPerGroup: one Int,
	minPerGroup: one Int,
	sub_students: one Int,
	registrationDeadline: one Date,
	submissionDeadline: one Date,
	creator: one Educator,
	tournament: one Tournament,
	var subscribedTeams: set Team,
	var status: one Status,
	var ranking : Student -> Int 
}{
// The score must be an int between 0 and 100
  all s: Student | ranking[s] >= 0 and ranking[s] <= 100
	minPerGroup <= maxPerGroup
	minPerGroup>=1
	maxPerGroup<=sub_students
	registrationDeadline.year <= submissionDeadline.year
	(registrationDeadline.year = submissionDeadline.year) implies
		(registrationDeadline.month <= submissionDeadline.month)
	(registrationDeadline.year = submissionDeadline.year && registrationDeadline.month = submissionDeadline.month) implies
		(registrationDeadline.day < submissionDeadline.day)
}

//Tournaments have a creator and a set of managers, in particular the creator of a tournament must always be part of the managers
sig Tournament{
	name: one String
	registrationDeadline: one Date
	creator: one Educator
	var managers: some Educator
	var battles: set Battle
	var students: set Student
	var status: one Status
	var ranking : Student -> Int
}{
// To impose positivity to the score
  	all s: Student | ranking[s] >= 0 	
	creator in managers

}



//Teams are composed of students and participate to battles, providing solutions
sig Team{
	members: some Student
	battle: one Battle 
	solutions: set Solution
	
}

//Teams provide solutions to the problems posed during battles, these solutions get automatically evaluated by the system
sig Solution{
	team: one Team,
	battle: one Battle,
	var score: one Int
}{

}

//Represents the status of a battle or a tournament
enum Status {Created, Ongoing, Closed}


FACTS
//A student can participate in a battle in only one team
fact NoOverlappingTeams{
all s1: Student, t1, t2: Team | 
    (s1 in t1.members and s1 in t2.members and t1.battle = t2.battle ) implies t1 = t2
}

fact UniqueTournamentNames {
  all disj t1, t2: Tournament | t1.name != t2.name
}

fact UniqueBattleNamesPerTournament {
  all t: Tournament |
    all disj b1, b2: Battle | b1, b2 in t.battles | b1.name != b2.name
}
fact SolutionScoreRange {
  all sol: Solution | sol.score >= 0 and sol.score <= 100
}
fact TeamMembershipLimit {
  all t: Team | 
      #t.members >= t.battle.minPerGroup and #t.members <= t.battle.maxPerGroup
}
fact UsernamenUnicity{
all disj u1, u2: User | u1.u_id!=u2_u_id and u1.email!=u2.email
}
fact TeamCoherenceInBattleAndSolution{
all disj b: Battle, s: Solution, t: Team| s.battle=b and s.team=t implies t in b.subscribedTeams and t.battle=b and s in t.solutions 
}



// dobbiamo garantire la coerenza del triangolo solutions, team, battle
