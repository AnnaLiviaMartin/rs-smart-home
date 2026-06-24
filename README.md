# Smart Home Verification with Alloy 6 and Lean

Dieses Projekt untersucht die formale Modellierung und Verifikation eines Smart-Home-Systems mit Fokus auf:

- Anwesenheitserkennung
- Zutritts- und Zugriffskontrolle
- Wetter- und Umweltsensorik

Zur Modellierung und Analyse wird **Alloy 6** und **Lean 4** verwendet.

## Ziele

Das Smart Home soll folgende Aspekte berücksichtigen:

### Schwerpunkt 1: Anwesenheitserkennung & Zugriffskontrolle

- Personen bewegen sich zwischen Räumen.
- Räume können eingeschränkt zugänglich sein.
- Zutritt erfolgt über unterschiedliche Authentifizierungsmechanismen.
- Berechtigungen können dauerhaft oder zeitlich begrenzt sein.
- Gäste erhalten temporäre Zugangsrechte.
- Unbefugter Zutritt soll erkannt werden.

### Schwerpunkt 2: Wetter- und Umweltsensoren

- Regen schließt Dachfenster.
- Hohe Windstärke fährt Markisen ein.
- Hohe Temperaturen schließen Rollläden.
- Schlechte Luftqualität aktiviert Lüftungssysteme.

## Projektstruktur

```text
project/
│
├── README.md
├── MODEL_SPECIFICATION.md
│
├── alloy/
│   ├── smart_home.als
│   └── scenarios.als
│
├── lean/
│   ├── SmartHome.lean
│   └── Proofs.lean
│
└── docs/
    └── diagrams/
```

## Installation

## Alloy ausführen

Modell laden:

```text
alloy/smart_home.als
```

Analyse starten:

```alloy
run {}
```

oder

```alloy
check PropertyName
```

---

## Lean ausführen

Projekt bauen:

```bash
lake build
```

Einzelne Datei prüfen:

```bash
lean SmartHome.lean
```

---

## Modellbeschreibung

Die fachliche Beschreibung des Smart-Home-Modells befindet sich in:

[MODEL_SPECIFICATION.md](MODEL_SPECIFICATION.md)

Dort werden definiert:

- Entitäten
- Zustände
- Beziehungen
- Sicherheitsregeln
- Sensorregeln
- Zu verifizierende Eigenschaften