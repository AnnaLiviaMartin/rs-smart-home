abstract sig Bool {}
one sig True, False extends Bool {}

abstract sig PERSON{
var	letzterRaum: lone RAUM
}
sig BEWOHNER extends PERSON {}
sig GAST extends PERSON {}

abstract sig ORT {
var 	personenImOrtGrob: set PERSON,
var	personenImOrtFein: set PERSON,
	nachbarn: some ORT
}

sig RAUM extends ORT {}{
	nachbarn in TUER
}

sig ZIMMER extends RAUM{}
sig GARTEN extends RAUM{}{
	one nachbarn //Garten soll nur einen Zugang zum Haus haben
}

sig AUTHENTIFIZIERUNG{}

sig TUER extends ORT{
var	offen: one Bool,
	authentifizierung: one AUTHENTIFIZIERUNG,
}{
	nachbarn in RAUM
	always offen = True
//	always #personenImOrtGrob = 0 //Damit keine Person im groben Modell ind er Tür stehen kann
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

fact jedeTuerHatEigenesAuthentifizierungsGeraet {
	all disj t1, t2: TUER | t1.authentifizierung not in t2.authentifizierung
}

fact tuerImmerOffenWennPersonEnthalten{
	always all t: TUER |  #(t.personenImOrtFein) >= 1 implies t.offen = True
}

//fact tuerKannKeinePersonenEnthalten_GROB{ //das Problem war, dass eine Person im Groben Modell sich in einer Tür befinden konnte.
//	always all t: TUER | no t.personenImOrtGrob
//}

fact personKannNurDurchOffeneTürGehen {
	always all t: TUER, p: PERSON | p in t.personenImOrtGrob implies t.offen = True
}

//türen und Räume sind immer symmetrisch
fact alleNachbarnSindSymmerisch {
	all r: RAUM, t: TUER | r in t.nachbarn <=> t in r.nachbarn
	all t:TUER, r: RAUM | t in r.nachbarn <=> r in t.nachbarn
}

fact tuerVerbindetZweiRaeume {
    all t: TUER | #t.nachbarn = 2
}

//################## init #################

pred init {
	//Am Anfang gitbt es keine Authentifizierten Personen, da alle im Garten stehen
	all p: PERSON | p in GARTEN.personenImOrtGrob
	all p: PERSON | p in GARTEN.personenImOrtFein
	all p: PERSON | p.letzterRaum = GARTEN
//	all t: TUER | t.offen = False
//	no AUTHENTICATION.authentifiziertePersone
}

//#################### invarianten Grob

pred moveGrob[p: PERSON, von, nach: RAUM]{
	//pre
	some t: TUER | t in von.nachbarn and t in nach.nachbarn and t.offen in True

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
	t.offen in True

	von.personenImOrtFein' = von.personenImOrtFein - p
	t.personenImOrtFein' = t.personenImOrtFein + p
	p.letzterRaum' = von

	all o: ORT - (von + t) | o.personenImOrtFein' = o.personenImOrtFein
}

pred verlasseTuer[p: PERSON, nach: RAUM, t: TUER]{
	p in t.personenImOrtFein
	nach in t.nachbarn
	p.letzterRaum != nach

	t.personenImOrtFein' = t.personenImOrtFein - p
	nach.personenImOrtFein' = nach.personenImOrtFein + p

	all o: ORT - (nach + t) | o.personenImOrtFein' = o.personenImOrtFein
}

pred vorbedingungenMove2 [r1, r2: RAUM, t: TUER] {
	r1 != r2
	r1 in t.nachbarn
	r2 in t.nachbarn
}

pred move2 {
	some p: PERSON, r1, r2: RAUM, t: TUER | ((betreteTuer[p, r1, t] and stutterGrob) or (verlasseTuer[p, r2, t] and moveGrob[p, r1, r2])) and vorbedingungenMove2[r1, r2, t]
}

pred stutter {
	all o: ORT | o.personenImOrtFein' = o.personenImOrtFein
	all o: ORT | o.personenImOrtGrob' = o.personenImOrtGrob
	all p: PERSON | p.letzterRaum' =  p.letzterRaum
}

pred show {
	init
	always move2
}

//run show for exactly 2 PERSON, 1 GAST, 1 BEWOHNER, exactly 2 ZIMMER, exactly 1 GARTEN, 2 AUTHENTIFIZIERUNG, exactly 2 TUER, exactly 3 RAUM

run show

//################ tests ######################

assert keineTeleportation_GROB {
	always all p: PERSON, von, nach: ORT | 
	(p in von.personenImOrtGrob and p in nach.personenImOrtGrob' implies (nach in von.nachbarn.nachbarn)) 
}

assert keineTeleportation_FEIN {
	always all p: PERSON, von, nach: ORT | 
	(p in von.personenImOrtFein and p in nach.personenImOrtFein' implies (nach in von.nachbarn)) or
	(p in von.personenImOrtFein and p in von.personenImOrtFein') //stutter
}

assert personIstNieInTuer_GROB {
	always all p: PERSON, t: TUER |
	(p not in t.personenImOrtGrob)
}

assert gleichesErgebnisInFreinUndGrob{
	always all p: PERSON, von: ORT |
		(p in von.personenImOrtGrob and p in von.personenImOrtFein) implies (p in von.personenImOrtGrob' and p in von.personenImOrtFein') or (p in von.personenImOrtGrob' and p in von.nachbarn.personenImOrtFein') or (p in von.nachbarn.nachbarn.personenImOrtGrob' and p in von.nachbarn.nachbarn.personenImOrtFein')
}

assert gleichesErgebnisInFreinUndGrob_V2 { //Hier gabe es die verbesserung, dass es nur einen Garten geben darf, da dies dre Anfangsraum für alle ist, die Personen aber auf diese zwei gärten initial unglecih aufgeteilt waren.
	always all p:PERSON, r: RAUM |
		p in r.personenImOrtFein implies p in r.personenImOrtGrob
}

check keineTeleportation_GROB for 4
check keineTeleportation_FEIN for 4
check personIstNieInTuer_GROB for 4
check gleichesErgebnisInFreinUndGrob for 4
check gleichesErgebnisInFreinUndGrob_V2 for 4

