abstract sig Bool {}
one sig True, False extends Bool {}

sig PERSON {}

abstract sig ORT {
	var	personenImOrt: set PERSON,
	nachbarn: some ORT
}

sig RAUM extends ORT {
	id: Int,
}{
	nachbarn in TUER
}

sig ZIMMER extends RAUM{
	authentication: one AUTHENTICATION,
}

sig GARTEN extends RAUM{
}{
	one nachbarn //Garten soll nur einen Zugang zum Haus haben
}

sig AUTHENTICATION{
	authentifiziertePersone: set PERSON
}

sig TUER extends ORT{
	maxPersonenAnzahl: 2,
	offen: one Bool
}{
	nachbarn in RAUM
	offen in True
}

//axiome

fact einePersonInGenauEinemRaum {
	always (all p: PERSON |
		#(p.~personenImOrt) = 1	
	)
}

fact personKannNurDurchOffeneTürGehen {
	always all t: TUER, p: PERSON | p in t.personenImOrt implies t.offen = True
}

//invarianten

pred init {
	//Am Anfang gitbt es keine Authentifizierten Personen, da alle im Garten stehen
	all p: PERSON | p in GARTEN.personenImOrt
	no AUTHENTICATION.authentifiziertePersone
}

pred tuerVerbindetZweiRaeume {
    all t: TUER | #t.nachbarn = 2
}

//türen und Räume sind immer symmetrisch
pred alleNachbarnSindSymmerisch {
	all r: RAUM, t: TUER | r in t.nachbarn <=> t in r.nachbarn
	all t:TUER, r: RAUM | t in r.nachbarn <=> r in t.nachbarn
}

//invarianten der Verfeinerung

pred wechselOrt[von, nach: ORT, p: PERSON] {
	//pre
	von != nach
	p in von.personenImOrt
	nach in von.nachbarn

	//post
	von.personenImOrt' = von.personenImOrt - p
	nach.personenImOrt' = nach.personenImOrt + p

	//frame
	all o:ORT - (von + nach)  | o.personenImOrt' = o.personenImOrt
}

pred stutter {
	all o: ORT | o.personenImOrt' = o.personenImOrt
}

pred skip[von, nach: ORT]{
	von.personenImOrt' = von.personenImOrt
	nach.personenImOrt' = nach.personenImOrt
}

pred move {
	some p: PERSON, von, nach: ORT | wechselOrt[von, nach, p] 
//	or skip[von, nach]
}

pred show {
init
tuerVerbindetZweiRaeume
alleNachbarnSindSymmerisch
always (move or stutter)
}

run show for exactly 2 PERSON, exactly 2 ZIMMER, exactly 1 GARTEN, 2 AUTHENTICATION, exactly 2 TUER, exactly 3 RAUM

// ############### checks und assertions #############

assert keineTeleportation {
	always all p: PERSON, von, nach: ORT | 
	(p in von.personenImOrt and p in nach.personenImOrt' implies (nach in von.nachbarn)) or
	(p in von.personenImOrt and p in von.personenImOrt') //stutter
}

check keineTeleportation for 4