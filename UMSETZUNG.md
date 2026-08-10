## Alloy-Modell und Analyse
Dieses Kapitel beschreibt, wie Alloy verwendet wird.

### Modellbestandteile

| Alloy-Konstrukt | Bedeutung |
| :--- | :--- |
| **sig** | Menge beziehungsweise Typ von Objekten |
| **extends** | Spezialisierung einer Menge |
| **fact** | Regel, die immer gelten muss |
| **pred** | Wiederverwendbare Operation oder Bedingung |
| **assert** | Zu überprüfende Behauptung |
| **check** | Prüfung einer Behauptung |
| **run** | Suche nach einem gültigen Beispiel |
| **always** | Eigenschaft gilt in allen Zuständen |

### Beispiel für eine Analyse

```alloy
assert keineTeleportation_FEIN {
    always all p: PERSON, von, nach: ORT |
        (p in von.personenImOrtFein and
         p in nach.personenImOrtFein')
        implies nach in von.nachbarn
}

check keineTeleportation_FEIN for 4
```

**Verständliche Erklärung**
Die Behauptung überprüft, dass eine Person nicht ohne eine entsprechende Verbindung von einem Ort zu einem anderen gelangen kann. Alloy sucht innerhalb einer festgelegten Modellgröße nach Gegenbeispielen. Wird kein Gegenbeispiel gefunden, gilt die Behauptung innerhalb dieses Suchraums als erfüllt. 

Wichtig ist dabei die Einschränkung: Ein erfolgreiches `check` ist bei Alloy kein allgemeiner mathematischer Beweis für alle möglichen Systemgrößen. Es bedeutet, dass innerhalb des gewählten Bereichs kein Gegenbeispiel gefunden wurde.

## Lean-Modell und formale Beweise
Der Aufbau sollte parallel zum Alloy-Kapitel erfolgen.

**Empfohlene Unterkapitel**
* Abbildung der Objekte aus Alloy nach Lean
* Definition von Zuständen
* Definition von Übergängen
* Formulierung der Invarianten
* Beweis ausgewählter Eigenschaften

**Unterschiede zwischen Alloy und Lean**
*Vergleichstabelle*

| Alloy | Lean |
| :--- | :--- |
| Suche nach Gegenbeispielen | Konstruktion formaler Beweise |
| Zustände und Relationen | Typen, Funktionen und Sätze |
| `check` | `theorem` beziehungsweise `lemma` |
| begrenzter Suchraum | grundsätzlich allgemeiner Beweis |
| Modellprüfung | interaktives beziehungsweise automatisiertes Beweisen |

**Beispielhafte Struktur**

```text
Zustand
 ├── Personen
 ├── Räume
 ├── Türen
 └── Öffnungszustände

Übergang
 ├── Tür betreten
 ├── Tür verlassen
 ├── Anmeldung
 └── Tür schließen

Eigenschaften
 ├── Jede Person ist genau an einem Ort
 ├── Keine Teleportation
 └── Grobes und feines Modell bleiben konsistent
```