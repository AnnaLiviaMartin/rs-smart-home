abstract sig Bool {}
one sig True, False extends Bool {}

sig PERSON {
var	letzterRaum: lone RAUM
}

abstract sig ORT {
var 	personenImOrtGrob: set PERSON,
var	personenImOrtFein: set PERSON,
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
}

//#################### axiome

fact genauEinenGarten {
	#GARTEN = 1
}

fact einePersonInGenauEinemOrt {
	always (all p: PERSON |
		#(p.~personenImOrtGrob) = 1	and
		#(p.~personenImOrtFein) = 1
	)
}

fact personKannNurDurchOffeneTürGehen {
	always all t: TUER, p: PERSON | p in t.personenImOrtGrob implies t.offen = True
}

//türen und Räume sind immer symmetrisch
fact alleNachbarnSindSymmerisch {
	all r: RAUM, t: TUER | r in t.nachbarn <=> t in r.nachbarn
	all t:TUER, r: RAUM | t in r.nachbarn <=> r in t.nachbarn
}

//#################### invarianten

pred init {
	//Am Anfang gitbt es keine Authentifizierten Personen, da alle im Garten stehen
	all p: PERSON | p in GARTEN.personenImOrtGrob
	all p: PERSON | p in GARTEN.personenImOrtFein
	no AUTHENTICATION.authentifiziertePersone
}

fact tuerVerbindetZweiRaeume {
    all t: TUER | #t.nachbarn = 2
}

pred moveGrob[p: PERSON, von, nach: RAUM]{
	//pre
	some t: TUER | t in von.nachbarn and t in nach.nachbarn

	//post
	von.personenImOrtGrob' = von.personenImOrtGrob - p
	nach.personenImOrtGrob' = nach.personenImOrtGrob + p

	//frame
	all o: RAUM - (von + nach)| o.personenImOrtGrob' = o.personenImOrtGrob
}

pred stutterGrob{
	all o: ORT | o.personenImOrtGrob' = o.personenImOrtGrob
}

//#################### invarianten der Verfeinerung -- alles was im feinen Modell funktioniert, muss auch im groben Modell funktionieren

pred betreteTuer[p: PERSON, von: RAUM, t: TUER]{
	p in von.personenImOrtFein
	t in von.nachbarn
//	t.offen = True

	von.personenImOrtFein' = von.personenImOrtFein - p
	t.personenImOrtFein' = t.personenImOrtFein + p

	all o: ORT - (von + t) | o.personenImOrtFein' = o.personenImOrtFein

	p.letzterRaum' = von
	all person: PERSON - p | p.letzterRaum' = person.letzterRaum
}

pred verlasseTuer[p: PERSON, nach: RAUM, t: TUER]{
	p in t.personenImOrtFein
	nach in t.nachbarn

	t.personenImOrtFein' = t.personenImOrtFein - p
	nach.personenImOrtFein' = nach.personenImOrtFein + p

	all o: ORT - (nach + t) | o.personenImOrtFein' = o.personenImOrtFein

	no p.letzterRaum'
	all person: PERSON - p | person.letzterRaum' = person.letzterRaum
}

pred personBetrittRaumSchritt{ //Hier brauchen wir stutter, da es im feinen modell die schritte Raum -> Tür -> Raum gibt und im groben modell nur Raum -> Raum
	some p: PERSON, von: RAUM, t: TUER | betreteTuer[p, von, t] and stutterGrob
}

pred personVerlaesstRaum{
	some p: PERSON, nach: RAUM, t: TUER | let von = p.letzterRaum | verlasseTuer[p, nach, t] and moveGrob[p, von,  nach]
}

pred next {
	personBetrittRaumSchritt or personVerlaesstRaum
}

pred stutter {
	all o: ORT | o.personenImOrtFein' = o.personenImOrtFein
}

pred show {
	init
	always (next)
}

run show for exactly 2 PERSON, exactly 2 ZIMMER, exactly 1 GARTEN, 2 AUTHENTICATION, exactly 2 TUER, exactly 3 RAUM

// ############### checks und assertions #############

assert keineTeleportation {
	always all p: PERSON, von, nach: ORT | 
	(p in von.personenImOrtGrob and p in nach.personenImOrtGrob' implies (nach in von.nachbarn)) or
	(p in von.personenImOrtGrob and p in von.personenImOrtGrob') //stutter
}

assert gleichesErgebnisInFreinUndGrob{
	always all p: PERSON, von: ORT |
		(p in von.personenImOrtGrob and p in von.personenImOrtFein) implies (p in von.personenImOrtGrob' and p in von.personenImOrtFein') or (p in von.personenImOrtGrob' and p in von.nachbarn.personenImOrtFein') or (p in von.nachbarn.nachbarn.personenImOrtGrob' and p in von.nachbarn.nachbarn.personenImOrtFein')
}

assert gleichesErgebnisInFreinUndGrob_V2 { //Hier gabe es die verbesserung, dass es nur einen Garten geben darf, da dies dre Anfangsraum für alle ist, die Personen aber auf diese zwei gärten initial unglecih aufgeteilt waren.
	always all p:PERSON, r: RAUM |
		p in r.personenImOrtFein implies p in r.personenImOrtGrob
}

check keineTeleportation for 4
check gleichesErgebnisInFreinUndGrob_V2 for 4