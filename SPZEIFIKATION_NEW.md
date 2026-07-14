
# Grobes Modell

- Ex gibt Orte, in denen sich Personen aufhalten können.
- Türen und Räume sind Orte
- Es gibt Räume, die sich in Garten und Zimmer aufteilen
- Alle Räume sind über Türen miteinander Verbunden
- Eine Person kann sich in genau einem Raum aufhalten
- Alle Personen befinden zunächst im Garten
- Ex existiert genau ein Garten
- Alle Nachbarschaftsbeziehungen der Räume und Türen sind symmetrisch
- Alle Räume haben Türen als Nachbarn und Türen haben nur Räume als Nachbarn
- Türen können offen oder geschlossen sein

## Logik
- Personen können in Räume wechseln, sofern die verbindende Tür geöffnet ist
- Beispiel : Raum -> Raum
_(Sofern es Personenstatus zulassen - muss später noch eingefügt werden)_

# Verfeinertes Modell 01 (Zutrittskontrolle)

- Jeder Raum hat ein eigenes Authentifizierungsgerät (Anwesenheitsliste)

## Logik 
- Eine Person muss, wenn sie in den Raum wechselt, durch eine geöffnete Tür gehen.
- Beispiel : Raum -> Tür -> Raum


# Verfeinertes Modell 02 (Physische Umsetzung)

## Logik
- Wenn eine Person zwischen Räumen wechseln will, kann sie die Tür öffnen mit dem Authentifizierungsgerät


## Idee für später:

- wenn eine Person die Tür über das Authentifizierungsgerät öffnet, könnte durch die offene tür eine weitere Person den Raum betreten
- Dazu müsste gleichzeitige Bewegung von Personen möglich sein.

## Verworfen:

- Person wechselt zwischen Räumen:
    1. Person muss sich am Authentifizierungsgerät anmelden
    2. Authentifizierungsgerät muss Eintritt gewähren
    3. Authentifizierungsgerät muss Person eintragen (sofern sie durchgeht?)
    
- Person wechselt zwischen Räumen:
    1. Nach gewährung des Eintritts (Vereinfachung 01.2) anmelden
    2. Authentifizierungsgerät entsperrt Tür
    3. Tür öffnen
    4. Person wechselt Raum
    5. Tür schließen
    3. Authentifizierungsgerät muss Person eintragen (sofern sie durchgegangen ist?)
    6. Tür verriegeln