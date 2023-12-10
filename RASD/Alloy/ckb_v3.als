//User are identifyied by a user id and divide themselves in students and educators
abstract sig User {
	u_id : one Int
}

sig Student extends User{}

sig Educator extends User{}

//Battles are created by educators for tournaments and students can form teams and participate to the battles
sig Battle{
	creator: one Educator,
	tournament: one Tournament,
	var subscribedTeams: set Team,
	var status: one Status
}

//Tournaments are created by an educator, who can grant managing permissions to other educators
//Students ccan subscribe to tournaments and take part in battles crreated by the managers
sig Tournament{
	creator: one Educator,
	var managers: some Educator,
	var battles: set Battle,
	var students: set Student,
	var status: one Status,
}{
	creator in managers
}

//A team is composed of students and can participate to a battle
sig Team{
	members: some Student,
	battle: one Battle,
}

//Teams propose solutions to the evauator, that assigns a score to each solution
sig Solution{
	team: one Team,
	score: one Int
}{
	score >= 0
	//score <= 100, Alloy can have integers of maximum value 7
}

//This enumeration represents the status of a battle or of a tournament:
// - Created status means that the battle/tournament has been created and students can subscribe to it
// - Ongoing means that the registration deadline has expired
// - Closed means that the submission deadline of the battle has expired or the creator of the tournamen has closed the competition
enum Status {Created, Ongoing, Closed}

//FACTS

//A student can participate in a battle in only one team
fact noOverlappingTeams{
	all s1: Student, t1, t2: Team | 
    		(s1 in t1.members and s1 in t2.members and t1.battle = t2.battle) implies t1 = t2
}

//There cannot be two users with the same name
fact usernameUnicity{
	all disj u1, u2: User | u1.u_id != u2.u_id
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

//A battle can belong only to one tournament
fact BattleTournamentConsistency{
	all b: Battle, t: Tournament |
		t = b.tournament iff b in t.battles
}

//A team can take part only in one battle
fact TeamBattleConsistency{
	all t: Team, b: Battle |
		t in b.subscribedTeams iff b = t.battle
}

//A tournament can be closed only when all its battles are closed
fact closedTournamentWhenClosedBattles{
	all t: Tournament |
		t.status = Closed implies (all b: Battle | b in t.battles implies b.status = Closed)
}

//If a team is subscribed to a battle, then all of its members are subscribed to the tournament of the battle
fact studentSubscriptionConsistency{
	all s: Student, t: Team, b: Battle |
		(s in t.members and t in b.subscribedTeams) implies
			s in b.tournament.students
}

//If a battle is in the Created status, then no team can provide solution for that battle
fact noSolutionForCreatedBattles{
	all b: Battle |
		b.status = Created implies (no s: Solution | s.team in b.subscribedTeams)
}

//If a tournament is in the Created status, then it cannot have any battle
fact noBattleForCreatedTournament{
	all t: Tournament |
		t.status = Created implies t.battles = none
}

pred show[]{}

run show for exactly 5 Student, 
			 exactly 2 Educator,
			 exactly 4 Battle,
			 exactly 3 Tournament,
			 exactly 4 Team,
			 exactly 5 Solution
