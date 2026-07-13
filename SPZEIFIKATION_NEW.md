
# Grobes Modell

- Es gibt Räume, die sich in Garten und Zimmer aufteilen
- Alle Räume sind über Türen miteinander Verbunden
- Eine Person kann sich in genau einem Raum aufhalten
- Alle Personen befinden zunächst im Garten
- Alle Nachbarschaftsbeziehungen der Räume und Türen sind symmetrisch

## Logik
- Personen können nur durch geöffnete Türen gehen
_(Sofern es Personenstatus zulassen - muss später noch eingefügt werden)_

# Verfeinertes Modell 01 (Zutrittskontrolle)

- Jeder Raum hat ein eigenes Authentifizierungsgerät (Anwesenheitsliste)

## Logik 
- Person wechselt zwischen Räumen:
    1. Person muss sich am Authentifizierungsgerät anmelden
    2. Authentifizierungsgerät muss Eintritt gewähren
    3. Authentifizierungsgerät muss Person eintragen (sofern sie durchgeht?)

# Verfeinertes Modell 02 (Physische Umsetzung)

## Logik
- Person wechselt zwischen Räumen:
    1. Nach gewährung des Eintritts (Vereinfachung 01.2) anmelden
    2. Authentifizierungsgerät entsperrt Tür
    3. Tür öffnen
    4. Person wechselt Raum
    5. Tür schließen
    3. Authentifizierungsgerät muss Person eintragen (sofern sie durchgegangen ist?)
    6. Tür verriegeln
