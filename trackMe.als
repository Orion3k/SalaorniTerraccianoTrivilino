
sig User {}

sig GroupOfUsers {
filteredUsers: set User
}

one sig Data4Help {
users: set User,
thirdParties: set ThirdParty,
allowAnonymous: set AnonymousPermission,
allowIndividual: set IndividualPermission
}

abstract sig ThirdParty {}

one sig AutomatedSOS extends ThirdParty {}

one sig Track4Run extends ThirdParty {}

abstract sig RequestStatus {}
sig ACCEPTED extends RequestStatus {}
sig REFUSED extends RequestStatus {}

sig IndividualPermission {
individualPermission: ThirdParty -> User,
status: lone RequestStatus
}

sig AnonymousPermission {
anonymousPermission: ThirdParty -> GroupOfUsers,
status: lone  RequestStatus
}

fact allRegistered {
	all u:User | (u in ThirdParty.(Data4Help. allowIndividual.individualPermission)) implies (u in Data4Help.users)
}

