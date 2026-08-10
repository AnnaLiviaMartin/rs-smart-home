# Formale Spezifikation und Verifikation eines Zutritts- und Bewegungssystems mit Alloy und Lean

Dieses Projekt beschreibt und überprüft ein Smart-Home-System zur Anwesenheitserkennung und Zutrittskontrolle.

Im Mittelpunkt stehen Personen, Räume, Türen und Authentifizierungseinrichtungen. Personen können sich zwischen Räumen bewegen. Der Zugang zu bestimmten Räumen wird über Türen kontrolliert.

Für die Modellierung und Analyse werden folgende Werkzeuge verwendet:

- **Alloy 6** zur Modellprüfung und zur Suche nach Gegenbeispielen
- **Lean 4** zur formalen Überprüfung und zum Beweisen ausgewählter Eigenschaften

## Dokumentation

Die Dokumentation ist auf mehrere Dateien verteilt. Diese README.md dient als Einstiegspunkt und gibt einen Überblick über das Projekt.

### Fachliche Idee und Motivation

Die Motivation, die fachliche Problemstellung und die Herleitung des Modells befinden sich in der [Idee.md](docs/Idee.md)

Dieses Dokument beschreibt unter anderem:

- das zugrunde liegende Problem,
- die beteiligten Personen und Orte,
- die Bewegungsmöglichkeiten,
- die Bedeutung der Türen,
- die Unterscheidung zwischen grobem und feinem Modell.

### Fachliche Spezifikation

Die fachlichen Regeln und Bedingungen des Systems befinden sich in [Model_Spezifikation.md](docs/Model_Spezifikation.md)

Dort wird das Modell zunächst unabhängig von Alloy und Lean beschrieben.

Behandelt werden unter anderem:

- Systemobjekte,
- Zustände,
- Bewegungsregeln,
- Türzustände,
- Authentifizierung,
- Invarianten,
- erwartete Systemabläufe.

### Umsetzungsentscheidungen

Die Beschreibung der konkreten Modellierungs- und Implementierungsentscheidungen befindet sich in [Umsetzung.md](docs/Umsetzung.md)

Dort wird erklärt, wie die fachlichen Anforderungen in Alloy und Lean umgesetzt wurden.

## Projektstruktur

Das Projekt ist wie folgt aufgebaut:

```text
project/
│
├── README.md
│
├── docs/
│   ├── Idee.md
│   ├── Model_Spezifikation.md
│   ├── Umsetzung.md
│   └── diagrams/
│   └── pictures/
│
├── alloy/
│   ├── smart_home.als
│   └── smart_home.thm
│
├── lean/
│   ├── SmartHome.lean
│   └── SmartHomeExamples.lean
```

### Verzeichnisse und Dateien

Die Umsetzungen befinden sich in den folgenden Verzeichnissen:

- [Alloy-Modell](alloy/)
- [Lean-Modell](lean/)

Das Alloy-Modell dient insbesondere dazu, mögliche Modellinstanzen zu erzeugen und Eigenschaften innerhalb eines begrenzten Suchraums zu überprüfen.

Lean wird verwendet, um ausgewählte Eigenschaften formal zu formulieren und zu beweisen.

Weitere wichtige Dateien, sind folgend aufgelistet:

| Pfad | Beschreibung |
| :--- | :--- |
| `docs/` | Ausführliche Projektdokumentation |
| `docs/diagrams/` | PlantUML-Diagramme |
| `docs/pictures/` | PlantUML-Bilder |
| `alloy/` | Alloy-Modell und zugehörige Darstellungsdateien |
| `lean/` | Lean-Definitionen, Beispiele und Beweise |
| `smart_home.als` | Formale Alloy-Spezifikation |
| `SmartHome.lean` | Formale Lean-Spezifikation |
| `SmartHomeExamples.lean` | Beispiele für die Lean-Spezifikation |



## Alloy ausführen

### Voraussetzungen

Für die Ausführung wird Alloy 6 benötigt.

### Ausführung

Modell laden:

```text
alloy/smart_home.als
```

Analyse starten:

```alloy
run {}
```

oder Eigenschaft überprüfen:

```alloy
check PropertyName
```

Die Style-Datei für's Ansehen des Alloy-Modells, findet sich unter ./alloy/todo.td

## Lean ausführen

### Voraussetzungen

Für die Ausführung wird Lean 4 mit Lake benötigt.

### Ausführung

Projekt bauen:

```bash
lake build
```

Einzelne Datei prüfen:

```bash
lean SmartHome.lean
```

Lean ist in zwei Dateien aufgesplittet. Die erste Datei todo.td stellt die Beweise bereit. Die zweite Datei todo2.td stellt ein Beispiel zur Verfügung.