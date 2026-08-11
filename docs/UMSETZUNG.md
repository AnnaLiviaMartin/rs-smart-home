# Umsetzungsentscheidungen

Dieses Dokument beschreibt die konkreten Modellierungs- und Implementierungsentscheidungen für das Smart-Home-System.

Die fachlichen Anforderungen sind in der [Modellspezifikation](./Modellspezifikation.md) beschrieben. Dieses Dokument erklärt, wie diese Anforderungen in Alloy und Lean umgesetzt wurden.

## Ziel der Umsetzung

Ziel der Umsetzung ist es, die drei fachlichen Modelle formal abzubilden:

1. das grobe Modell mit direkten Bewegungen zwischen Räumen,
2. das erste verfeinerte Modell mit dem Aufenthalt in einer Tür,
3. das zweite verfeinerte Modell mit Authentifizierung und Türsteuerung.

Alloy wird verwendet, um mögliche Zustände und Abläufe automatisch zu untersuchen. Lean wird verwendet, um ausgewählte Eigenschaften formal zu beweisen.

## Verwendete Werkzeuge

### Alloy

Alloy wird für die automatische Zustands- und Ablaufanalyse verwendet.

Mit Alloy werden insbesondere folgende Eigenschaften untersucht:

- Jede Person befindet sich genau an einem Ort.
- Jede Tür verbindet genau zwei Räume.
- Bewegungen sind nur über verbundene Räume möglich.
- Geschlossene Türen können nicht ohne Authentifizierung passiert werden.
- Ereignisse verletzen keine Systemgarantien.

### Lean

Lean wird für mathematische Beweise verwendet.

In Lean werden insbesondere folgende Eigenschaften betrachtet:

- Die Invarianten bleiben nach einer Bewegung erhalten.
- Eine Person befindet sich nach einer Bewegung weiterhin genau an einem Ort.
- Eine Tür verbindet weiterhin genau zwei Räume.
- Eine fehlgeschlagene Authentifizierung verändert den Zustand nicht.
- Die Verfeinerung liefert dasselbe fachliche Ergebnis wie das grobe Modell.

## Alloy-Modelle

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

### Abbildung der Objekte

### Vereinfachungen und Grenzen

## Lean-Modelle

Dieses Kapitel beschreibt, wie Lean verwendet wird.

### Abbildung der Objekte aus Alloy nach Lean

### Definition von Zuständen

### Definition von Übergängen

### Formulierung der Invarianten

### Beweis ausgewählter Eigenschaften

## Unterschiede zwischen Alloy und Lean**
*Vergleichstabelle*

| Alloy | Lean |
| :--- | :--- |
| Suche nach Gegenbeispielen | Konstruktion formaler Beweise |
| Zustände und Relationen | Typen, Funktionen und Sätze |
| `check` | `theorem` beziehungsweise `lemma` |
| begrenzter Suchraum | grundsätzlich allgemeiner Beweis |
| Modellprüfung | interaktives beziehungsweise automatisiertes Beweisen |