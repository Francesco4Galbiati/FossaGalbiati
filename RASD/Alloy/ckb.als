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
	tournamentCreated: set Tournament,
	tournamentManaged: set Tournament
}

//Students can participate in tournaments and in battles through teams
sig Student extends User{
	tournaments: set Tournament,
	teams: set Team,
	battles: set Battle
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
	description: one String,
	var ranking : Student -> Score
}{
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
	var ranking : Student -> Score
}{
	creator in managers

}

//Teams are composed of students and participate to battles, providing solutions
sig Team{
	members: some Student
	battles: some Battle //perchè some? Anche se in un'altra battaglia si forma una squadra con le stesse persone dobbiamo comunque considerarlo un team diverso...
	solutions: set Solution
}

//Teams provide solutions to the problems posed during battles, these solutions get automatically evaluated by the system
sig Solution{
	team: one Team
	battle: one Battle
	var score: one Int
}{
	score >= 0 and score <= 100
}

//Represents the status of a battle or a tournament
enum Status {Created, Ongoing, Closed}
