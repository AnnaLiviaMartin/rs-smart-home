# Modelspezifikation

Dieses Dokument beschreibt die fachliche Modellierung des Smart-Home-Systems unabhängig von der konkreten Umsetzung in Alloy oder Lean. Die Modelle werden schrittweise nach dem Event-B-Vorgehen verfeinert.

Jede Verfeinerungsstufe übernimmt die Elemente und Eigenschaften des vorherigen Modells und ergänzt weitere Details. Bereits eingeführte Objekte und Systemgarantien bleiben daher in den folgenden Modellen erhalten.

# Grobes Modell

Das grobe Modell beschreibt nur den direkten Wechsel einer Person zwischen zwei Räumen. Die Tür wird dabei als Verbindung zwischen den Räumen betrachtet, nicht jedoch als eigener Aufenthaltsort.

## Objekte und Beziehungen
- Es gibt Orte, in denen sich Personen aufhalten können.
- Orte unterteilen sich in Räume und Türen.
- Räume unterteilen sich in Gärten und Zimmer.
- Alle Räume sind über Türen miteinander Verbunden
- Räume und Türen können über Nachbarschaftsbeziehungen miteinander verbunden sein.
- Nachbarschaftsbeziehungen sind symmetrisch.
- Eine Person kann sich in genau einem Raum aufhalten
- Alle Personen befinden initial im Garten
- Es existiert genau ein Garten
- Alle Nachbarschaftsbeziehungen der Räume und Türen sind symmetrisch
- Alle Räume haben Türen als Nachbarn und Türen haben nur Räume als Nachbarn
- Jede Tür kann geöffnet oder geschlossen sein.

## Systemgarantien
- Eine Person kann nicht gleichzeitig mehreren Räumen zugeordnet sein.
- Eine Tür verbindet genau zwei verschiedene Räume.
- Eine Tür kann nicht direkt mit einer anderen Tür verbunden sein.
- Bewegungen zwischen nicht verbundenen Räumen sind nicht möglich.

## Ereignis `bewege`
Eine Person kann direkt von einem Raum in einen anderen wechseln, wenn:

- sich die Person im Ausgangsraum befindet,
- der Zielraum über eine Tür mit dem Ausgangsraum verbunden ist,
- die Tür geöffnet ist.

# Verfeinertes Modell 01 (Zutrittskontrolle)

Das erste verfeinerte Modell ergänzt den tatsächlichen Bewegungsablauf. Eine Tür ist nun nicht mehr nur eine Verbindung, sondern auch ein möglicher Aufenthaltsort.

## Zusätzliche Systemregel

Im verfeinerten Modell befindet sich eine Person während des Durchgangs vorübergehend in der Tür. Deshalb kann sich eine Person entweder in einem Raum oder in einer Tür befinden.

## Ereignis `betreteTuer`

Eine Person kann eine Tür betreten, wenn:

- sie sich in einem mit der Tür verbundenen Raum befindet,
- die Tür geöffnet ist.

Anschließend wird die Person aus dem Raum entfernt und der Tür zugeordnet.

## Ereignis `verlasseTuer`

Eine Person kann eine Tür verlassen, wenn:

- sie sich in der Tür befindet,
- die Tür mit dem Zielraum verbunden ist.
- Anschließend wird die Person aus der Tür entfernt und dem Zielraum zugeordnet.

# Verfeinertes Modell 02 (Physische Umsetzung)

## Objekte und Beziehungen

- Jede Tür besitzt genau ein Authentifizierungsgerät.
- Es gibt zwei Personentypen: Bewohner:innen und Gäste.
- Bewohner:innen besitzen eine dauerhafte Berechtigung zum Öffnen geschlossener Türen.
- Gäste besitzen keine dauerhafte Berechtigung zum Öffnen geschlossener Türen.
- Jede Tür besitzt einen Öffnungszustand, welcher durch das Authentifizieren beeinflussbar ist.

## Ereignis `authentifizieren`

Eine Person kann sich an einer Tür authentifizieren, wenn:

- sie sich in einem an die Tür angrenzenden Raum befindet,
- die Tür geschlossen ist,
- die Person eine gültige Berechtigung besitzt.

Bei einer erfolgreichen Authentifizierung wird die Tür geöffnet. Authentifizierung schließt niemals Türen, sondern öffnet diese nur. Geöffnete Türen fallen irgendwann wieder zu.

## Beispielabläufe

**Tür geschlossen**
Gast -> auth -> x
Bewohner -> auth -> Tür -> Raum

**Tür offen**
Gast -> auth -> Tür -> Raum
Bewohner -> auth -> Tür -> Raum