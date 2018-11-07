open util/relation

sig User {
allowedThirdParties: set ThirdParty
}

sig GroupOfUsers {
filteredUsers: set User
}

one sig Data4Help {
subscription: set Subscription,
individual: set IndividualPermission
}

sig ThirdParty {
allowedIndividual: set User,
allowedAnonymazed: set GroupOfUsers
}

one sig AutomatedSOS extends ThirdParty {}

one sig Track4Run extends ThirdParty {}

abstract sig RequestStatus {}
one sig ACCEPTED extends RequestStatus {}
one sig REFUSED extends RequestStatus {}

sig IndividualPermission {
individualPermission: ThirdParty -> User,
status: lone RequestStatus
}{ #individualPermission = 1 }

sig AnonymousPermission {
anonymousPermission: ThirdParty -> GroupOfUsers,
status: lone  RequestStatus
}
sig Subscription extends AnonymousPermission { }

fact anonymousSingleRequestCondition {
(all ap: AnonymousPermission | #ThirdParty.(ap.anonymousPermission) > 1000 iff ap.status = ACCEPTED) and
(all ap: AnonymousPermission | #ThirdParty.(ap.anonymousPermission) <= 1000 iff ap.status =REFUSED)
}

fact subscriptionCondition {
all s: Subscription | s in Data4Help.subscription and s.status = ACCEPTED
}

fact individualRequestCondition{
all pi: IndividualPermission | pi in Data4Help.individual and (pi.status = ACCEPTED or  pi.status = REFUSED)
}

fact b {
(all tp:ThirdParty, u: User | tp in u.allowedThirdParties and u in tp.allowedIndividual iff 
(one ip:IndividualPermission | tp in dom[ip.individualPermission] and ThirdParty.(ip.individualPermission) = u and ip.status = ACCEPTED))
	and 
	( all tp:ThirdParty, u: User | !(tp in u.allowedThirdParties and u in tp.allowedIndividual)  iff
	 (no ip:IndividualPermission | (tp in dom[ip.individualPermission] and ThirdParty.(ip.individualPermission) = u)) )
}













