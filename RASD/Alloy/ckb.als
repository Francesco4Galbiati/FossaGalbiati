//SIGNATURES

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
	var battlesCreated: set Battle,
	var tournamentsCreated: set Tournament,
	var tournamentsManaged: set Tournament
}{
	#tournamentsManaged >= #tournamentsCreated
}

//Students can participate in tournaments and in battles through teams
sig Student extends User{
	var tournaments: set Tournament,
	var battles: set Battle,
	var teams: set Team
	
}{
	#battles = #teams
}


//Battles have some parameters that need to be inserted by the creator, these parameters must respect the constraints stated in the facts below
sig Battle{
	name: one String,
	maxPerGroup: one Int,
	minPerGroup: one Int,
	var sub_students: one Int,
	registrationDeadline: one Date,
	submissionDeadline: one Date,
	creator: one Educator,
	tournament: one Tournament,
	var subscribedTeams: set Team,
	var status: one Status,
	var ranking : Student -> Int 
}{
	//this facts ensure consistency between the attributeds regarding the subscribed students
	minPerGroup * #subscribedTeams <= sub_students
	sub_students <= maxPerGroup * #subscribedTeams
	sub_students = sum t: subscribedTeams | #t.members
	#ranking = sub_students
	minPerGroup <= maxPerGroup
	maxPerGroup <= sub_students
	minPerGroup >= 1

	// The score must be an int between 0 and 100
  	all s: Student | ranking[s] >= 0 and ranking[s] <= 100

	//the registration deadline must come before the submission deadline
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
	//The score must be greater or equal than 0
  	all s: Student | ranking[s] >= 0

	//The creator of the tournament is also a manager
	creator in managers
}

//Teams are composed of students and participate to battles, providing solutions
sig Team{
	members: some Student
	battle: one Battle 
	var solutions: set Solution
}

//Teams provide solutions to the problems posed during battles, these solutions get automatically evaluated by the system
sig Solution{
	team: one Team,
	battle: one Battle,
	score: one Int
}{
	//scores are between 0 and 100
 	score >= 0
	score <= 100
}

//Represents the status of a battle or a tournament
enum Status {Created, Ongoing, Closed}

//PREDICATES

//An educator can create a tournament
pred createTournament[e: Educator, t: Tournament]{
	no t2: Tournament | t2 != t1 implies t2.name = t.name
	t.status = Created
	t.creator = e
	e in t.managers
	t.battles = none
	t.students = none
	ranking = none

	t not in e.createdTournaments
	t in e.createdTournaments'
	t not in e.managedTournaments
	t in e.managedTournaments'
}

//An educator can create a battle for a tournament
pred createBattle[e: Educator, b: Battle, t: Tournament]{
	all b2: Battle | (b2 in t.battles and b2 != b) implies b2.name != b.name
	b.status = Created
	b.creator = e
	b in t.battles
	t = b.tournament
	e in t.managers
	t in e.managedTournaments
	b.subscribedTeams = none
	b.ranking = none

	b not in e.createdBattles
	b in e.createdBattles'
}

//After the registration deadline, the tournament starts
pred startTournament[t: Tournament]{
	t.status = Created
	t.status' = Ongoing
}

//The creator can close an ongoing tournament
pred closeTournament[t: Tournament]{
	t.status = Ongoing
	t.status' = Closed
}

//A battle starts when the registration deadline expires
pred startBattle[b: Battle]{
	b.status = Created
	b.status' = Ongoing
}

//A battle is closed when the submission deadline expires
pred closeBattle[b: Battle]{
	b.status = Ongoing
	b.status' = Closed
}

//students can enroll in tourbnaments before the registration deadline
pred enrollStudent(s: Student, t: Tournament) {
	t.status = Created
 	s not in t.students 
 	t.students' = t.students + s
  	t not in s.tournaments
 	s.tournaments' = s.tournaments + t
}

//team of students can join battles
pred TeamJoinsBattle[t: Team, b: Battle] {
    	b.status = Created
    	(all s: Student | s in t.members implies s in b.tournament.students) 
    	t not in b.subscribedTeams 
   	b.subscribedTeams' = b.subscribedTeams + t
	b.sub_students' = b.sub_students + #t.members
	(all s: Student | s in t.members implies b not in s.battles)
	(all s: Student | s in t.members implies s.battles' = s.battles + t.members)
}

//the creator of a tournament can grant permission to other colleagues
pred AddManagerToTournament[e: Educator, t: Tournament] {
    	e not in t.managers
    	t.managers' = t.managers + e
	t not in e.tournamentsManaged
	e.tournamentsManaged' = e.tournamentsManaged + t
}

//the creator of a tournament can revoke permission from other colleagues
pred RemoveManagerFromTournament[e: Educator, t: Tournament] {
    	e in t.managers
    	t.managers' = t.managers - e
	t in e.tournamentsManaged
	e.tournamentsManaged' = e.tournamentsManaged - t
}

//FACTS

//A student can participate in a battle in only one team
fact NoOverlappingTeams{
	all s1: Student, t1, t2: Team | 
    		(s1 in t1.members and s1 in t2.members and t1.battle = t2.battle) implies t1 = t2
}

//There cannot be two tournaments with the same name
fact UniqueTournamentNames {
  	all disj t1, t2: Tournament | t1.name != t2.name
}

//There cannot be two battles with the same name in a single tournament
fact UniqueBattleNamesPerTournament {
  	all t: Tournament | all disj b1, b2: Battle | 
		b1, b2 in t.battles implies b1.name != b2.name
}

//Every team taking part to a battle must have its number of members between the upper and lower bounds of the battle
fact TeamMembershipLimit {
  	all t: Team | 
      		#t.members >= t.battle.minPerGroup and #t.members <= t.battle.maxPerGroup
}

//There cannot be two users with the same name
fact UsernamenUnicity{
	all disj u1, u2: User | u1.u_id != u2_u_id and u1.email != u2.email
}

//If a team presents a solution for a battle, that team must be part of the battle
fact TeamCoherenceInBattleAndSolution{
	all disj b: Battle, s: Solution, t: Team | 
		(s.battle = b and s.team = t) implies 
			(t in b.subscribedTeams and t.battle = b and s in t.solutions)
}

//If a student is part of a team and that team is subscribed to a battle belonging to a tournament, then the student must be subscribed to the tournament
fact teamSubscribedToTournament{
	all s: Student, tm: Team, tr: Tournament | 
		(s in tm.members and tm.battle in tr.battles) implies
			(s in tr.students)
}

//If an educator creates a battle for a tournament, it must be a manager of that tournament
fact battleCreatorIsManager{
	all e: Educator, b: Battle, t: Tournament |
		(b.creator = e and b in t.battles) implies
			(e in t.managers)
}

//1. An educator is the creator of a tournament if and only if the tournament is created by that educator
//2. An educator is the creator of a battle if and only if the battle is created by that educator
fact educatorConsistency{
	all e: Educator, t: Tournament |
		(e = t.creator iff t in e.tournamentsCreated) and
			(e in t.managers iff t in e.tournamentsManaged)
	all e: Educator, b:Battle |
		(e = b.creator iff b in e.battlesCreated)
}

//1. A student is subscribed to a tournament if and only if that student is in the set of subscribed students of that tournament
//2. A student is part of a team if and only if the student is in the members of that team
//3. A student is subscribed to a battle if and only if the student is part of a team subscribed to that battle
fact studentConsistency{
	all s: Student, t: Tournament |
		(s in t.students iff t in s.tournaments)
	all s: Student, t: Team |
		(s in t.members iff t in s.teams)
	all s: Student, b: Battle|
		(b in s.battles iff (one t: Team | s in t.members and t in b.teams))
}

//The score of a student in a tournament is the sum of the scores of that student in all the battles of the tournament
fact StudentScoreInTournament {
    all t: Tournament, s: Student | 
        s in t.students implies 
            t.ranking[s] = sum b: t.battles | b.ranking[s] | b in s.battles
}

//A battle in a tournament must have a number of participants smaller or equal than the number of participants in the tournament
fact StudentsInTournamentsAndBattles{
	all t: Tournament, b: Battle |
		b in t.battles implies #t.students >= b.sub_students
}

//Models the status evolution of a tournament
fact tournamentStatus{
	all t: Tournament |
		(t.status = Created implies (once createTournament[t.creator, t])) and
		(t.status = Created implies historically t.status = Created) and
		(t.status = Created implies eventually t.status = Ongoing) and
		(t.status = Created implies eventually t.status = Closed) and
		(t.status = Ongoing implies once startTournament[t]) and
		(t.status = Ongoing implies eventually t.status = Closed) and
		(t.status = Closed implies once startTournament[t]) and
		(t.status = Closed implies once closeTournament[t]) and
		(t.status = Closed implies after always t.status = Closed)
}

//Models the status evolution of a battle
fact battleStatus{
	all b: Battles |
		(b.status = Created implies (once createBattle[b.creator, b, b.tournament])) and
		(b.status = Created implies historically b.status = Created) and
		(b.status = Created implies eventually b.status = Ongoing) and
		(b.status = Created implies eventually b.status = Closed) and
		(b.status = Ongoing implies once startBattle[b]) and
		(b.status = Ongoing implies eventually b.status = Closed) and
		(b.status = Closed implies once startBattle[b]) and
		(b.status = Closed implies once closeBattle[b]) and
		(b.status = Closed implies after always b.status = Closed)
}

//If an educator is a manager of a tournament, then it must haave been granted the permission at some point in time
fact managerOnceAdded{
	all e: Educator, t: Tournament |
		e in t.managers implies once AddManagerToTournament[e, t]
}

//If an educator is not a manager of a tournament, then either it was never granted the permission or the permission have been revoked at some point in time
fact notManagerRemovedOrNeverAdded{
	all e: Educator, t: Tournament |
		e not in t.managers implies
			(once removeManagerFromTournament[e, t] or
			 historically e not in t.managers)
}

//If a student is subscribed to a tournament, then it must have subscribed at some point in time
fact studentOnceEnrolled{
	all s: Student, t: Tournament |
		s in t.students implies once enrollStudent[s, t]
}

//If a team is taking part in a battle, then it must have been subscribed at some point in time
fact teamOnceSubscribed{
	all t: Team, b: Battle |
		t in b.subscribedTeams implies once teamJoinsBattle[t, b]
}
