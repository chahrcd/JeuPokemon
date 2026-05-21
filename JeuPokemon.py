import json
import math
import random
import struct
import tempfile
import tkinter as tk
import wave
from dataclasses import dataclass
from pathlib import Path
from tkinter import ttk
from urllib.request import urlretrieve

try:
    import pygame
except ImportError:
    pygame = None

try:
    import winsound
except ImportError:
    winsound = None


TYPE_ALIASES = {
    "electrik": "electrique",
    "electric": "electrique",
}

TYPE_TRANSLATIONS = {
    "normal": "normal",
    "fire": "feu",
    "water": "eau",
    "electric": "electrique",
    "grass": "plante",
    "ice": "glace",
    "steel": "acier",
    "fighting": "combat",
    "poison": "poison",
    "ground": "sol",
    "flying": "vol",
    "psychic": "psy",
    "bug": "insecte",
    "rock": "roche",
    "ghost": "spectre",
    "dragon": "dragon",
}

EFFICACITES = {
    "normal": {"roche": 0.5, "spectre": 0},
    "feu": {
        "feu": 0.5,
        "eau": 0.5,
        "plante": 2,
        "glace": 2,
        "insecte": 2,
        "roche": 0.5,
        "dragon": 0.5,
    },
    "eau": {"feu": 2, "eau": 0.5, "plante": 0.5, "sol": 2, "roche": 2, "dragon": 0.5},
    "electrique": {"eau": 2, "electrique": 0.5, "plante": 0.5, "sol": 0, "vol": 2, "dragon": 0.5},
    "plante": {
        "feu": 0.5,
        "eau": 2,
        "plante": 0.5,
        "sol": 2,
        "roche": 2,
        "vol": 0.5,
        "insecte": 0.5,
        "dragon": 0.5,
    },
    "glace": {"feu": 0.5, "eau": 0.5, "plante": 2, "sol": 2, "vol": 2, "dragon": 2},
    "combat": {"normal": 2, "glace": 2, "roche": 2, "tenebres": 2, "poison": 0.5, "vol": 0.5, "psy": 0.5, "spectre": 0},
    "poison": {"plante": 2, "poison": 0.5, "sol": 0.5, "roche": 0.5, "spectre": 0.5},
    "sol": {"feu": 2, "electrique": 2, "plante": 0.5, "poison": 2, "vol": 0, "roche": 2},
    "vol": {"electrique": 0.5, "plante": 2, "combat": 2, "insecte": 2, "roche": 0.5},
    "psy": {"combat": 2, "poison": 2, "psy": 0.5},
    "insecte": {"feu": 0.5, "plante": 2, "combat": 0.5, "poison": 2, "vol": 0.5, "psy": 2, "spectre": 0.5},
    "roche": {"feu": 2, "glace": 2, "combat": 0.5, "sol": 0.5, "vol": 2, "insecte": 2},
    "spectre": {"normal": 0, "psy": 0, "spectre": 2},
    "dragon": {"dragon": 2},
}

RANDOM_FACTOR_MIN = 0.95
RANDOM_FACTOR_MAX = 1.0
TEAM_SIZE = 3

ITEM_POTION_MAX = "Potion Max"
ITEM_BOUCLIER_PRISMA = "Bouclier Prisma"
ITEM_ORBE_FURIE = "Orbe Furie"


@dataclass
class Pokemon:
    name: str
    type_pokemon: str


@dataclass
class FighterState:
    pokemon: Pokemon
    hp: int
    stats: dict


class PokemonBattleGUI:
    def __init__(self, root):
        self.root = root
        self.root.title("Pokemon")
        self.root.geometry("1040x700")
        self.root.minsize(980, 660)
        self.root.configure(bg="#F5F2FF")

        self.attack_name = "Charge"
        self.attack_types = sorted(set(TYPE_TRANSLATIONS.values()))
        self.attack_type_p1 = tk.StringVar(value="plante")
        self.attack_type_p2 = tk.StringVar(value="plante")
        self.attack_power = 40

        self.round_min = 3
        self.round_max = 5
        self.round_index = 0
        self.finished = False

        self.special_items = [
            ITEM_POTION_MAX,
            ITEM_BOUCLIER_PRISMA,
            ITEM_ORBE_FURIE,
        ]

        pokedex_entries = self.load_pokedex_entries()
        self.pokedex_by_name = {
            entry.get("name"): entry
            for entry in pokedex_entries
            if entry.get("name")
        }

        self.pokemon_names = sorted(self.pokedex_by_name.keys())

        self.strength_by_name = {
            name: self.compute_strength_score(name)
            for name in self.pokemon_names
        }

        default_1, default_2 = self.get_default_selected_names()

        self.selected_name1 = tk.StringVar(value=default_1)
        self.selected_name2 = tk.StringVar(value=default_2)
        self.selected_item1 = tk.StringVar(value=self.special_items[0])
        self.selected_item2 = tk.StringVar(value=self.special_items[0])
        self.music_enabled = True
        self.music_volume = 0.35
        self.music_file = None
        self.music_backend = None
        self.sprite_cache = {}
        self.music_credit_var = tk.StringVar(value="Credits musique: non renseignes")
        self.switched_this_round = {1: False, 2: False}

        self.build_ui()
        self.start_music()
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)
        self.start_battle()

    def get_default_selected_names(self):
        default_1 = "Bulbizarre" if "Bulbizarre" in self.pokedex_by_name else (self.pokemon_names[0] if self.pokemon_names else "Bulbizarre")
        default_2 = "Pikachu" if "Pikachu" in self.pokedex_by_name else (self.pokemon_names[1] if len(self.pokemon_names) > 1 else default_1)
        return default_1, default_2

    def get_fighter_max_hp(self, fighter):
        return fighter.stats.get("max_hp", fighter.hp)

    def get_active_fighters(self):
        return self.team1[self.active_idx1], self.team2[self.active_idx2]


    @staticmethod
    def set_state(widgets, state):
        for widget in widgets:
            widget.configure(state=state)

    def reset_battle_state(self):
        self.round_index = 0
        self.finished = False
        self.pending_attack_boost = {1: 1.0, 2: 1.0}
        self.pending_shield = {1: 1.0, 2: 1.0}
        self.used_items = {1: set(), 2: set()}
        self.switched_this_round = {1: False, 2: False}

    def make_fighter_team(self, pokemons):
        team = []
        for pokemon in pokemons:
            hp, stats = self.get_stats(pokemon)
            full_stats = dict(stats)
            full_stats["max_hp"] = hp
            team.append(FighterState(pokemon, hp, full_stats))
        return team

    def can_switch(self, team, active_idx, player_index):
        return not self.finished and self.has_alternative_switch(team, active_idx) and not self.switched_this_round[player_index]

    def all_ko(self, team):
        return not any(fighter.hp > 0 for fighter in team)

    def get_alive_indices(self, team):
        return [i for i, f in enumerate(team) if f.hp > 0]

    def total_team_hp(self, team):
        return sum(max(f.hp, 0) for f in team)

    @staticmethod
    def has_alternative_switch(team, active_idx):
        return any(i != active_idx and f.hp > 0 for i, f in enumerate(team))

    @staticmethod
    def format_team_status(team, active_idx):
        def line(i, f):
            marker = ">" if (i - 1) == active_idx else " "
            hp = max(f.hp, 0)
            max_hp = f.stats.get("max_hp", f.hp)
            state = "K.O." if f.hp <= 0 else f"{hp}/{max_hp}"
            return f"{marker} {i}. {f.pokemon.name} [{state}]"
        return "\n".join(line(i, f) for i, f in enumerate(team, start=1))

    def update_team_labels(self):
        self.team1_label.configure(text=self.format_team_status(self.team1, self.active_idx1))
        self.team2_label.configure(text=self.format_team_status(self.team2, self.active_idx2))

    def reset_round_switches(self):
        self.switched_this_round = {1: False, 2: False}

    def manual_switch(self, player_index):
        if self.finished:
            return

        if self.switched_this_round.get(player_index):
            self.log(f"Joueur {player_index}: changement deja utilise ce round.")
            return

        team = self.team1 if player_index == 1 else self.team2
        active_idx = self.active_idx1 if player_index == 1 else self.active_idx2
        side = player_index
        next_idx = next((i for i in range(active_idx + 1, len(team)) if team[i].hp > 0), None)
        if next_idx is None:
            next_idx = next((i for i, fighter in enumerate(team) if fighter.hp > 0 and i != active_idx), None)
        if next_idx is None:
            self.log(f"Joueur {player_index}: aucun Pokemon disponible pour changer.")
            return
        if player_index == 1:
            self.active_idx1 = next_idx
        else:
            self.active_idx2 = next_idx

        self.pending_attack_boost[player_index] = 1.0
        self.pending_shield[player_index] = 1.0

        self.set_active_sprite(side)
        self.switched_this_round[player_index] = True
        self.refresh_status()
        self.log(f"Joueur {player_index} change de Pokemon -> {team[next_idx].pokemon.name}")

    def show_result_popup(self, winner, team1_hp, team2_hp):
        popup = tk.Toplevel(self.root)
        popup.title("Resultat du combat")
        popup.geometry("420x250")
        popup.configure(bg="#F5F2FF")
        popup.resizable(False, False)
        popup.transient(self.root)
        popup.grab_set()

        frame = ttk.Frame(popup, padding=14)
        frame.pack(fill="both", expand=True)

        ttk.Label(frame, text="Combat termine", style="Title.TLabel").pack(pady=(0, 10))
        ttk.Label(frame, text=f"Vainqueur: {winner}", style="Name.TLabel").pack(pady=(0, 8))
        ttk.Label(frame, text=f"PV equipe Joueur 1: {team1_hp}", style="Info.TLabel").pack(anchor="w")
        ttk.Label(frame, text=f"PV equipe Joueur 2: {team2_hp}", style="Info.TLabel").pack(anchor="w")

        ttk.Button(frame, text="Fermer", style="Game.TButton", command=popup.destroy).pack(pady=(16, 0))

    def build_team(self, starter_name, forbidden_names=None):
        if not self.pokemon_names:
            return [self.create_pokemon(starter_name)]

        forbidden_names = set(forbidden_names or [])
        available = [name for name in self.pokemon_names if name != starter_name and name not in forbidden_names]

        sorted_candidates = self.sort_by_strength_distance(starter_name, available)

        preferred_size = max(8, min(20, len(sorted_candidates)))
        chosen_names = [starter_name]

        pool = sorted_candidates[:preferred_size]
        random.shuffle(pool)
        chosen_names.extend(pool[: TEAM_SIZE - len(chosen_names)])

        if len(chosen_names) < TEAM_SIZE:
            leftovers = [name for name in available if name not in chosen_names]
            random.shuffle(leftovers)
            chosen_names.extend(leftovers[: TEAM_SIZE - len(chosen_names)])

        return [self.create_pokemon(name) for name in chosen_names[:TEAM_SIZE]]

    def set_active_sprite(self, side):
        fighter = self.team1[self.active_idx1] if side == 1 else self.team2[self.active_idx2]
        sprite = self.load_sprite(fighter.pokemon.name)
        if side == 1:
            self.sprite1 = sprite
            label = self.image1_label
        else:
            self.sprite2 = sprite
            label = self.image2_label

        if sprite is not None:
            label.configure(image=sprite, text="")
        else:
            label.configure(image="", text="(image indisponible)")

    def handle_team_ko_switches(self):
        switched = False
        for side, team, active_idx_attr, player_label in (
            (1, self.team1, "active_idx1", "Joueur 1"),
            (2, self.team2, "active_idx2", "Joueur 2"),
        ):
            active_idx = getattr(self, active_idx_attr)
            if team[active_idx].hp > 0:
                continue

            next_idx = next((i for i, fighter in enumerate(team) if fighter.hp > 0), None)
            if next_idx is None or next_idx == active_idx:
                continue

            setattr(self, active_idx_attr, next_idx)
            self.log(f"{team[next_idx].pokemon.name} entre en jeu pour {player_label}")
            self.set_active_sprite(side)
            switched = True

        if switched:
            self.refresh_status()

    def build_ui(self):
        self.configure_styles()

        container = ttk.Frame(self.root, style="Main.TFrame", padding=14)
        container.pack(fill="both", expand=True)

        self.create_header(container)
        self.create_selector_section(container)
        self.create_players_section(container)
        self.create_controls_section(container)
        self.create_log_section(container)

        if winsound is None and pygame is None:
            self.music_btn.configure(text="Musique indisponible", state="disabled")

    def create_header(self, container):
        header = ttk.Frame(container, style="Header.TFrame", padding=(14, 10))
        header.pack(fill="x", pady=(0, 10))
        ttk.Label(header, text="Combat de Pokemon", style="Title.TLabel").pack(anchor="center")

    def create_selector_section(self, container):
        selector_frame = ttk.LabelFrame(container, text="Selection des Pokemon", style="Card.TLabelframe", padding=10)
        selector_frame.pack(fill="x", pady=(0, 10))

        ttk.Label(selector_frame, text="Pokemon 1:", style="Info.TLabel").grid(row=0, column=0, sticky="w", padx=(0, 8))
        self.combo_p1 = ttk.Combobox(selector_frame, textvariable=self.selected_name1, values=self.pokemon_names, state="readonly", width=24, style="Game.TCombobox")
        self.combo_p1.grid(row=0, column=1, sticky="w", padx=(0, 20))
        self.combo_p1.bind("<<ComboboxSelected>>", self.on_selection_change)

        ttk.Label(selector_frame, text="Pokemon 2:", style="Info.TLabel").grid(row=0, column=2, sticky="w", padx=(0, 8))
        self.combo_p2 = ttk.Combobox(selector_frame, textvariable=self.selected_name2, values=self.pokemon_names, state="readonly", width=24, style="Game.TCombobox")
        self.combo_p2.grid(row=0, column=3, sticky="w", padx=(0, 20))
        self.combo_p2.bind("<<ComboboxSelected>>", self.on_selection_change)

        ttk.Button(selector_frame, text="Choix aleatoire", style="Game.TButton", command=self.random_selection).grid(row=0, column=4, sticky="e", padx=(0, 8))
        selector_frame.columnconfigure(6, weight=1)

    def create_players_section(self, container):
        top = ttk.Frame(container, style="Main.TFrame")
        top.pack(fill="x")

        (
            self.name1,
            self.hp1_label,
            self.hp1_bar,
            self.image1_label,
            self.team1_label,
            self.item1_box,
            self.item_combo_1,
            self.item_btn_1,
            self.switch_btn_1,
        ) = self.create_player_panel(
            top,
            title="Joueur 1",
            anchor="w",
            progress_style="P1.Horizontal.TProgressbar",
            item_var=self.selected_item1,
            player_index=1,
            pad_x=(0, 6),
        )

        (
            self.name2,
            self.hp2_label,
            self.hp2_bar,
            self.image2_label,
            self.team2_label,
            self.item2_box,
            self.item_combo_2,
            self.item_btn_2,
            self.switch_btn_2,
        ) = self.create_player_panel(
            top,
            title="Joueur 2",
            anchor="e",
            progress_style="P2.Horizontal.TProgressbar",
            item_var=self.selected_item2,
            player_index=2,
            pad_x=(6, 0),
        )

    def create_player_panel(self, parent, title, anchor, progress_style, item_var, player_index, pad_x):
        panel = ttk.LabelFrame(parent, text=title, style="Card.TLabelframe", padding=10)
        panel.pack(side="left", fill="x", expand=True, padx=pad_x)

        name = ttk.Label(panel, style="Name.TLabel")
        name.pack(anchor=anchor)

        hp_label = ttk.Label(panel, style="Info.TLabel")
        hp_label.pack(anchor=anchor, pady=(2, 6))

        hp_bar = ttk.Progressbar(panel, orient="horizontal", mode="determinate", length=300, style=progress_style)
        hp_bar.pack(anchor=anchor)

        image_label = ttk.Label(panel, style="Info.TLabel")
        image_label.pack(anchor=anchor, pady=(10, 0))

        team_label = ttk.Label(panel, style="Info.TLabel", justify="left")
        team_label.pack(anchor=anchor, pady=(8, 0))

        item_box = ttk.Frame(panel, style="Card.TFrame")
        item_box.pack(anchor=anchor, pady=(8, 0))

        ttk.Label(item_box, text="Objet special:", style="Info.TLabel").pack(side="left", padx=(0, 6))

        item_combo = ttk.Combobox(item_box, textvariable=item_var, values=self.special_items, state="readonly", width=16, style="Game.TCombobox")
        item_combo.pack(side="left", padx=(0, 6))

        item_btn = ttk.Button(item_box, text="Utiliser", style="Game.TButton", command=lambda: self.use_special_item(player_index))
        item_btn.pack(side="left")

        switch_btn = ttk.Button(item_box, text="Changer", style="Game.TButton", command=lambda: self.manual_switch(player_index))
        switch_btn.pack(side="left", padx=(6, 0))

        return name, hp_label, hp_bar, image_label, team_label, item_box, item_combo, item_btn, switch_btn

    def create_controls_section(self, container):
        controls = ttk.Frame(container, style="Controls.TFrame", padding=10)
        controls.pack(fill="x", pady=(14, 10))

        self.round_label = ttk.Label(controls, text="Round: 0/5", style="Info.TLabel")
        self.round_label.pack(side="left", padx=(0, 10))

        self.round_progress = ttk.Progressbar(controls, orient="horizontal", mode="determinate", length=280, maximum=self.round_max, style="Round.Horizontal.TProgressbar")
        self.round_progress.pack(side="left", padx=(0, 14))

        atk_types_frame = ttk.Frame(controls, style="Controls.TFrame")
        atk_types_frame.pack(side="left", padx=(0, 12))

        ttk.Label(atk_types_frame, text="Type J1:", style="Info.TLabel").pack(side="left", padx=(0, 4))
        self.attack_type_combo_1 = ttk.Combobox(atk_types_frame, textvariable=self.attack_type_p1, values=self.attack_types, state="readonly", width=10, style="Game.TCombobox")
        self.attack_type_combo_1.pack(side="left", padx=(0, 10))

        ttk.Label(atk_types_frame, text="Type J2:", style="Info.TLabel").pack(side="left", padx=(0, 4))
        self.attack_type_combo_2 = ttk.Combobox(atk_types_frame, textvariable=self.attack_type_p2, values=self.attack_types, state="readonly", width=10, style="Game.TCombobox")
        self.attack_type_combo_2.pack(side="left")

        self.next_btn = ttk.Button(controls, text="Tour suivant", style="Accent.TButton", command=self.play_round)
        self.next_btn.pack(side="right", padx=(8, 0))

        ttk.Button(controls, text="Recommencer", style="Game.TButton", command=self.start_battle).pack(side="right")
        self.music_btn = ttk.Button(controls, text="Musique: ON", style="Game.TButton", command=self.toggle_music)
        self.music_btn.pack(side="right", padx=(0, 8))

        ttk.Label(container, textvariable=self.music_credit_var, style="Credit.TLabel").pack(anchor="w", pady=(0, 8), padx=(2, 0))

    def create_log_section(self, container):
        log_frame = ttk.LabelFrame(container, text="Journal du combat", style="Card.TLabelframe", padding=10)
        log_frame.pack(fill="both", expand=True)

        self.log_text = tk.Text(
            log_frame,
            height=16,
            wrap="word",
            font=("Consolas", 10),
            bg="#FFFFFF",
            fg="#46577B",
            insertbackground="#46577B",
            relief="flat",
            padx=8,
            pady=8,
        )
        self.log_text.pack(side="left", fill="both", expand=True)

        log_scroll = ttk.Scrollbar(log_frame, orient="vertical", command=self.log_text.yview)
        log_scroll.pack(side="right", fill="y")
        self.log_text.configure(yscrollcommand=log_scroll.set)

        self.log_text.tag_configure("headline", foreground="#86668A")
        self.log_text.tag_configure("event", foreground="#5C77B2")
        self.log_text.configure(state="disabled")

    def configure_styles(self):
        style = ttk.Style()
        style.theme_use("clam")

        style.configure("Main.TFrame", background="#F5F2FF")
        style.configure("Card.TFrame", background="#FDFBFF")
        style.configure("Controls.TFrame", background="#EEF3FF")
        style.configure("Header.TFrame", background="#E9EEFF")

        style.configure("Title.TLabel", font=("Trebuchet MS", 26, "bold"), background="#E9EEFF", foreground="#3E4B73")
        style.configure("Subtitle.TLabel", font=("Trebuchet MS", 11, "bold"), background="#E9EEFF", foreground="#5C6D94")
        style.configure("Credit.TLabel", font=("Trebuchet MS", 10), background="#EEF3FF", foreground="#6F719A")
        style.configure("Name.TLabel", font=("Trebuchet MS", 16, "bold"), background="#FDFBFF", foreground="#3C4A66")
        style.configure("Info.TLabel", font=("Trebuchet MS", 11), background="#FDFBFF", foreground="#586782")
        style.configure("Badge.TLabel", font=("Trebuchet MS", 10, "bold"), background="#DDE8FF", foreground="#4D628F", padding=(10, 4))

        style.configure("Card.TLabelframe", background="#FDFBFF", bordercolor="#C8D5F0", relief="solid", borderwidth=1)
        style.configure("Card.TLabelframe.Label", background="#FDFBFF", foreground="#6077A6", font=("Trebuchet MS", 10, "bold"))

        style.configure("Game.TButton", font=("Trebuchet MS", 10, "bold"), padding=8, background="#9BBDF9", foreground="#24365E", borderwidth=0)
        style.map("Game.TButton", background=[("active", "#AFCBFF"), ("disabled", "#CFD8EE")])

        style.configure("Accent.TButton", font=("Trebuchet MS", 10, "bold"), padding=8, background="#F7BCCB", foreground="#5C3340", borderwidth=0)
        style.map("Accent.TButton", background=[("active", "#F9CDD8"), ("disabled", "#DFCCD2")])

        style.configure("P1.Horizontal.TProgressbar", troughcolor="#E5EAF8", background="#A9E3BF", lightcolor="#A9E3BF", darkcolor="#8BCFA8", bordercolor="#FDFBFF")
        style.configure("P2.Horizontal.TProgressbar", troughcolor="#E5EAF8", background="#AFCFF9", lightcolor="#AFCFF9", darkcolor="#8DB6EA", bordercolor="#FDFBFF")
        style.configure("Round.Horizontal.TProgressbar", troughcolor="#E5EAF8", background="#F6E0A8", lightcolor="#F6E0A8", darkcolor="#E7CB82")

        style.configure(
            "Game.TCombobox",
            fieldbackground="#FFFFFF",
            background="#FFFFFF",
            foreground="#44557A",
            arrowcolor="#6D83B8",
            selectbackground="#DDE8FF",
            selectforeground="#3F4F72",
        )

    def ensure_fallback_music(self):
        fallback_path = Path(tempfile.gettempdir()) / "pokemon_battle_theme.wav"
        if fallback_path.exists():
            return fallback_path

        sample_rate = 22050
        duration_sec = 8
        volume = 0.22
        notes = [261.63, 329.63, 392.00, 329.63, 293.66, 369.99, 440.00, 369.99]

        with wave.open(str(fallback_path), "w") as wav_file:
            wav_file.setnchannels(1)
            wav_file.setsampwidth(2)
            wav_file.setframerate(sample_rate)

            frames = []
            for i in range(sample_rate * duration_sec):
                t = i / sample_rate
                note_idx = int(t * 2) % len(notes)
                freq = notes[note_idx]
                tone = (
                    math.sin(2 * math.pi * freq * t)
                    + 0.55 * math.sin(2 * math.pi * (freq / 2) * t)
                    + 0.35 * math.sin(2 * math.pi * (freq * 1.5) * t)
                )
                sample = int(32767 * volume * tone / 2)
                frames.append(struct.pack("<h", sample))
            wav_file.writeframes(b"".join(frames))

        return fallback_path

    def resolve_music_file(self, allow_mp3=True):
        candidates = [
            Path(__file__).with_name("assets") / "battle_theme.mp3",
            Path(__file__).with_name("assets") / "music.mp3",
            Path(__file__).with_name("battle_theme.mp3"),
            Path(__file__).with_name("music.mp3"),
            Path(__file__).with_name("battle_theme.wav"),
            Path(__file__).with_name("music.wav"),
            Path("c:/Users/Charlotte/Desktop/Pokemon/battle_theme.mp3"),
            Path("c:/Users/Charlotte/Desktop/Pokemon/battle_theme.wav"),
            Path("c:/Users/Charlotte/Downloads/Pokemon - Main Theme (Krale Remix).mp3"),
        ]
        for path in candidates:
            if not allow_mp3 and path.suffix.lower() == ".mp3":
                continue
            if path.exists():
                return path
        return self.ensure_fallback_music()

    def load_music_credit_text(self):
        default_credit = "Credits musique: Pokemon - Main Theme (Krale Remix)"
        candidates = [
            Path(__file__).with_name("music_credits.json"),
            Path(__file__).with_name("assets") / "music_credits.json",
        ]

        for path in candidates:
            if not path.exists():
                continue
            try:
                with path.open("r", encoding="utf-8") as f:
                    data = json.load(f)
                if isinstance(data, dict):
                    title = str(data.get("title", "")).strip()
                    artist = str(data.get("artist", "")).strip()
                    source = str(data.get("source", "")).strip()
                    parts = [
                        title,
                        f"par {artist}" if artist else "",
                        f"source: {source}" if source else "",
                    ]
                    parts = [part for part in parts if part]

                    if parts:
                        return "Credits musique: " + " | ".join(parts)
            except Exception:
                continue

        return default_credit

    def update_music_credit_label(self):
        self.music_credit_var.set(self.load_music_credit_text())

    def start_music(self):
        try:
            backend_started = False

            if pygame is not None:
                try:
                    self.music_file = self.resolve_music_file(allow_mp3=True)
                    if not pygame.mixer.get_init():
                        pygame.mixer.init()
                    pygame.mixer.music.load(str(self.music_file))
                    pygame.mixer.music.set_volume(self.music_volume)
                    pygame.mixer.music.play(-1)
                    self.music_backend = "pygame"
                    backend_started = True
                except Exception:
                    pass

            if not backend_started and winsound is not None:
                self.music_file = self.resolve_music_file(allow_mp3=False)
                options = winsound.SND_FILENAME | winsound.SND_ASYNC | winsound.SND_LOOP
                winsound.PlaySound(str(self.music_file), options)
                self.music_backend = "winsound"
                backend_started = True

            if not backend_started:
                raise RuntimeError("Pas de moteur audio disponible")

            self.music_enabled = True
            self.update_music_credit_label()
            if hasattr(self, "music_btn"):
                self.music_btn.configure(text="Musique: ON")
        except Exception:
            self.music_enabled = False
            self.music_backend = None
            self.music_credit_var.set("Credits musique: impossible de charger la musique")
            if hasattr(self, "music_btn"):
                self.music_btn.configure(text="Musique indisponible", state="disabled")

    def stop_music(self):
        if self.music_backend == "pygame" and pygame is not None:
            try:
                if pygame.mixer.get_init():
                    pygame.mixer.music.stop()
            except Exception:
                pass
        elif self.music_backend == "winsound" and winsound is not None:
            winsound.PlaySound(None, winsound.SND_PURGE)

    def toggle_music(self):
        if winsound is None and pygame is None:
            return
        if self.music_enabled:
            self.stop_music()
            self.music_enabled = False
            self.music_btn.configure(text="Musique: OFF")
        else:
            self.start_music()

    def on_close(self):
        self.stop_music()
        self.root.destroy()

    def load_pokedex_entries(self):
        paths = [
            Path(__file__).with_name("pokedex.json"),
            Path("c:/Users/Charlotte/Desktop/Pokemon/pokedex.json"),
        ]
        for path in paths:
            if not path.exists():
                continue
            try:
                with path.open("r", encoding="utf-8") as f:
                    data = json.load(f)
                if isinstance(data, list):
                    return data
            except Exception:
                continue
        return []

    @staticmethod
    def normalize_type(type_name):
        value = str(type_name).strip().lower()
        return TYPE_ALIASES.get(value, value)

    def create_pokemon(self, pokemon_name):
        entry = self.pokedex_by_name.get(pokemon_name, {})
        raw_types = entry.get("type", [])
        first_type = str(raw_types[0]).strip().lower() if isinstance(raw_types, list) and raw_types else "normal"
        mapped = TYPE_TRANSLATIONS.get(first_type, first_type)
        return Pokemon(pokemon_name, mapped)

    def get_stats(self, pokemon):
        base = self.pokedex_by_name.get(pokemon.name, {}).get("base", {})
        hp = self.to_int_stat(base.get("HP", 50), 50)
        stats = {
            "attaque": self.to_int_stat(base.get("Attack", 50), 50),
            "defense": self.to_int_stat(base.get("Defense", 50), 50),
            "niveau": self.to_int_stat(base.get("Level", 50), 50),
        }
        return hp, stats

    @staticmethod
    def to_int_stat(value, default=50):
        try:
            return int(value)
        except (TypeError, ValueError):
            return default

    def compute_strength_score(self, pokemon_name):
        entry = self.pokedex_by_name.get(pokemon_name, {})
        base = entry.get("base", {})
        hp = self.to_int_stat(base.get("HP", 50), 50)
        attack = self.to_int_stat(base.get("Attack", 50), 50)
        defense = self.to_int_stat(base.get("Defense", 50), 50)
        level = self.to_int_stat(base.get("Level", 50), 50)
        return float((hp * 1.1) + (attack * 1.35) + (defense * 1.1) + (level * 0.45))

    def get_strength_score(self, pokemon_name):
        cached = self.strength_by_name.get(pokemon_name)
        if cached is not None:
            return cached
        score = self.compute_strength_score(pokemon_name)
        self.strength_by_name[pokemon_name] = score
        return score

    def sort_by_strength_distance(self, reference_name, candidates):
        reference_score = self.get_strength_score(reference_name)
        return sorted(candidates, key=lambda name: abs(self.get_strength_score(name) - reference_score))

    def choose_balanced_opponent(self, first_name):
        candidates = [name for name in self.pokemon_names if name != first_name]
        
        if not candidates:
            return first_name

        scored = self.sort_by_strength_distance(first_name, candidates)

        pool_size = min(len(scored), max(4, len(scored) // 5))
        preferred_pool = scored[:pool_size]
        return random.choice(preferred_pool)

    def get_effectiveness(self, attack_type, defend_type):
        atk = self.normalize_type(attack_type)
        dfn = self.normalize_type(defend_type)
        return EFFICACITES.get(atk, {}).get(dfn, 1)

    def calc_damage(self, level, attack, power, defense, stab, effectiveness):
        critical = 1.5 if random.random() < 0.15 else 1.0
        random_factor = random.uniform(RANDOM_FACTOR_MIN, RANDOM_FACTOR_MAX)
        coefficient = stab * effectiveness * critical * random_factor
        scaled_level = int(level * 0.4 + 2)
        base = int(int(int(int(scaled_level * attack) * power) / max(1, defense)) / 50) + 2
        damage = max(1, int(base * coefficient))
        return damage, critical, effectiveness

    def ensure_distinct_selection(self):
        name1 = self.selected_name1.get().strip()
        name2 = self.selected_name2.get().strip()

        if not name1 or not name2:
            return False
        if name1 != name2:
            return True

        candidate = next((value for value in self.pokemon_names if value != name1), None)
        if candidate is not None:
            self.selected_name2.set(candidate)
            return True
        return False

    def on_selection_change(self, _event=None):
        self.ensure_distinct_selection()

    def apply_selection(self):
        if self.ensure_distinct_selection():
            self.start_battle()
            return

        self.clear_log()
        self.log("Impossible de lancer le combat: il faut deux Pokemon differents.")

    def random_selection(self):
        if not self.pokemon_names:
            return
        if len(self.pokemon_names) == 1:
            self.selected_name1.set(self.pokemon_names[0])
            self.selected_name2.set(self.pokemon_names[0])
            self.clear_log()
            self.log("Un seul Pokemon disponible: combat aleatoire impossible.")
            return

        name1 = random.choice(self.pokemon_names)
        name2 = self.choose_balanced_opponent(name1)
        self.selected_name1.set(name1)
        self.selected_name2.set(name2)
        self.apply_selection()

    def load_sprite(self, pokemon_name):
        cached = self.sprite_cache.get(pokemon_name)
        if cached is not None:
            return cached

        entry = self.pokedex_by_name.get(pokemon_name, {})
        pokemon_id = entry.get("id")
        if pokemon_id is None:
            return None

        try:
            cache_dir = Path(tempfile.gettempdir()) / "pokemon_sprites"
            cache_dir.mkdir(parents=True, exist_ok=True)
            local_file = cache_dir / f"{pokemon_id}.png"
            if not local_file.exists():
                url = f"https://raw.githubusercontent.com/PokeAPI/sprites/master/sprites/pokemon/{pokemon_id}.png"
                urlretrieve(url, local_file)
            sprite = tk.PhotoImage(file=str(local_file))
            self.sprite_cache[pokemon_name] = sprite
            return sprite
        except Exception:
            return None

    def start_battle(self):
        if not self.ensure_distinct_selection():
            self.clear_log()
            self.log("Impossible de lancer le combat: il faut deux Pokemon differents.")
            self.next_btn.configure(state="disabled")
            self.set_state((self.item_btn_1, self.item_btn_2, self.switch_btn_1, self.switch_btn_2), "disabled")
            return

        starter1 = self.selected_name1.get().strip()
        starter2 = self.selected_name2.get().strip()

        self.team1_pokemon = self.build_team(starter1, forbidden_names={starter2})
        team1_names = {pokemon.name for pokemon in self.team1_pokemon}
        self.team2_pokemon = self.build_team(starter2, forbidden_names=team1_names)

        self.team1 = self.make_fighter_team(self.team1_pokemon)
        self.team2 = self.make_fighter_team(self.team2_pokemon)

        self.active_idx1 = 0
        self.active_idx2 = 0
        self.reset_battle_state()

        self.set_active_sprite(1)
        self.set_active_sprite(2)

        self.refresh_status()
        self.clear_log()
        self.log(f"Debut du combat {len(self.team1)}v{len(self.team2)}")
        self.log(f"Equipe Joueur 1: {', '.join(f.pokemon.name for f in self.team1)}")
        self.log(f"Equipe Joueur 2: {', '.join(f.pokemon.name for f in self.team2)}")
        self.log("Regle: minimum 3 rounds avant KO, maximum 5 rounds.")
        self.log(f"Objets speciaux: {ITEM_POTION_MAX} (+soin), {ITEM_BOUCLIER_PRISMA} (-40% prochain degat), {ITEM_ORBE_FURIE} (+50% prochaine attaque).")
        self.next_btn.configure(state="normal")
        self.set_state((self.item_btn_1, self.item_btn_2, self.switch_btn_1, self.switch_btn_2), "normal")

    def refresh_status(self):
        f1, f2 = self.get_active_fighters()
        size1 = max(1, len(self.team1))
        size2 = max(1, len(self.team2))
        alive1 = sum(f.hp > 0 for f in self.team1)
        alive2 = sum(f.hp > 0 for f in self.team2)

        self.name1.configure(text=f"{f1.pokemon.name} ({self.active_idx1 + 1}/{size1})")
        self.name2.configure(text=f"{f2.pokemon.name} ({self.active_idx2 + 1}/{size2})")
        self.hp1_label.configure(text=f"PV: {max(f1.hp, 0)} / {self.get_fighter_max_hp(f1)} | Restants: {alive1}/{size1}")
        self.hp2_label.configure(text=f"PV: {max(f2.hp, 0)} / {self.get_fighter_max_hp(f2)} | Restants: {alive2}/{size2}")
        self.hp1_bar.configure(maximum=self.get_fighter_max_hp(f1))
        self.hp2_bar.configure(maximum=self.get_fighter_max_hp(f2))
        self.hp1_bar["value"] = max(f1.hp, 0)
        self.hp2_bar["value"] = max(f2.hp, 0)
        self.round_label.configure(text=f"Round: {self.round_index}/{self.round_max}")
        self.round_progress["value"] = self.round_index
        self.update_team_labels()

        can_switch_1 = self.can_switch(self.team1, self.active_idx1, 1)
        can_switch_2 = self.can_switch(self.team2, self.active_idx2, 2)

        self.switch_btn_1.configure(state="normal" if can_switch_1 else "disabled")
        self.switch_btn_2.configure(state="normal" if can_switch_2 else "disabled")

    def clear_log(self):
        self.log_text.configure(state="normal")
        self.log_text.delete("1.0", "end")
        self.log_text.configure(state="disabled")

    def log(self, text):
        self.log_text.configure(state="normal")
        if text.startswith("==="):
            self.log_text.insert("end", text + "\n", "headline")
        elif text.startswith("---"):
            self.log_text.insert("end", text + "\n", "event")
        else:
            self.log_text.insert("end", text + "\n")
        self.log_text.see("end")
        self.log_text.configure(state="disabled")

    def use_special_item(self, fighter_index):
        if self.finished:
            return

        fighter = self.team1[self.active_idx1] if fighter_index == 1 else self.team2[self.active_idx2]
        selected_item = (self.selected_item1 if fighter_index == 1 else self.selected_item2).get()

        max_hp = self.get_fighter_max_hp(fighter)

        if selected_item in self.used_items[fighter_index]:
            self.log(f"{fighter.pokemon.name} a deja utilise {selected_item}.")
            return

        self.used_items[fighter_index].add(selected_item)

        if selected_item == ITEM_POTION_MAX:
            heal_amount = int(max_hp * 0.35) + 15
            before_hp = fighter.hp
            fighter.hp = min(max_hp, fighter.hp + heal_amount)
            healed = fighter.hp - before_hp
            self.log(f"{fighter.pokemon.name} utilise {ITEM_POTION_MAX}: +{healed} PV")
        elif selected_item == ITEM_BOUCLIER_PRISMA:
            self.pending_shield[fighter_index] = 0.6
            self.log(f"{fighter.pokemon.name} active {ITEM_BOUCLIER_PRISMA}: prochain degat reduit de 40%")
        elif selected_item == ITEM_ORBE_FURIE:
            self.pending_attack_boost[fighter_index] = 1.5
            self.log(f"{fighter.pokemon.name} active {ITEM_ORBE_FURIE}: prochaine attaque +50%")

        self.refresh_status()

    def attack_once(self, attacker, defender, attacker_idx, defender_idx):
        power = int(self.attack_power * self.pending_attack_boost[attacker_idx])
        if self.pending_attack_boost[attacker_idx] > 1:
            self.log(f"  Bonus d'attaque actif pour {attacker.pokemon.name}")
        self.pending_attack_boost[attacker_idx] = 1.0

        attack_type = self.attack_type_p1.get() if attacker_idx == 1 else self.attack_type_p2.get()
        attack_type = self.normalize_type(attack_type or "normal")

        attacker_type_norm = self.normalize_type(attacker.pokemon.type_pokemon)
        stab = 1.5 if attack_type == attacker_type_norm else 1.0

        effectiveness = self.get_effectiveness(attack_type, defender.pokemon.type_pokemon)
        ko_allowed = self.round_index >= self.round_min

        damage, critical, effectiveness = self.calc_damage(
            attacker.stats["niveau"],
            attacker.stats["attaque"],
            power,
            defender.stats["defense"],
            stab,
            effectiveness,
        )

        damage = max(1, int(damage * self.pending_shield[defender_idx]))
        if self.pending_shield[defender_idx] < 1.0:
            self.log(f"  {ITEM_BOUCLIER_PRISMA} absorbe une partie des degats de {defender.pokemon.name}")
        self.pending_shield[defender_idx] = 1.0

        defender.hp -= damage
        if not ko_allowed:
            defender.hp = max(defender.hp, 1)

        self.log(f"{attacker.pokemon.name} utilise {self.attack_name} ({attack_type}) sur {defender.pokemon.name} -> {damage} degats")
        if critical > 1:
            self.log("  Coup critique x1.5")
        if effectiveness > 1:
            self.log("  C'est super efficace")
        elif effectiveness < 1:
            self.log("  Ce n'est pas tres efficace")
        if defender.hp <= 0:
            self.log(f"  {defender.pokemon.name} est K.O.")

        return damage

    def play_round(self):
        if self.finished:
            return

        if self.round_index >= self.round_max:
            self.finish_battle()
            return

        self.switched_this_round = {1: False, 2: False}
        self.refresh_status()

        self.round_index += 1
        self.log("")
        self.log(f"--- Round {self.round_index} ---")

        f1, f2 = self.get_active_fighters()

        dmg_1_to_2 = self.attack_once(f1, f2, 1, 2)
        self.handle_team_ko_switches()

        f1, f2 = self.get_active_fighters()
        if f2.hp > 0:
            dmg_2_to_1 = self.attack_once(f2, f1, 2, 1)
            self.handle_team_ko_switches()
        else:
            dmg_2_to_1 = 0
            self.log(f"{f2.pokemon.name} ne peut pas attaquer (K.O.)")

        f1, f2 = self.get_active_fighters()
        self.log(
            f"Bilan round {self.round_index}: {f1.pokemon.name} / {f2.pokemon.name} | "
            f"degats J1->{dmg_1_to_2} | degats J2->{dmg_2_to_1}"
        )

        self.refresh_status()

        team1_ko = self.all_ko(self.team1)
        team2_ko = self.all_ko(self.team2)
        if self.round_index >= self.round_min and (team1_ko or team2_ko):
            self.finish_battle()
            return

        if self.round_index >= self.round_max:
            self.finish_battle()

    def finish_battle(self):
        if self.finished:
            return

        self.finished = True
        self.next_btn.configure(state="disabled")
        self.set_state((self.item_btn_1, self.item_btn_2, self.switch_btn_1, self.switch_btn_2), "disabled")

        team1_total_hp = self.total_team_hp(self.team1)
        team2_total_hp = self.total_team_hp(self.team2)
        winner = "Joueur 1" if team1_total_hp > team2_total_hp else ("Joueur 2" if team2_total_hp > team1_total_hp else "Egalite")

        self.log("")
        self.log("=== Combat termine ===")
        self.log(f"Le gagnant du combat est: {winner}")
        self.log(f"PV finaux equipes -> Joueur 1: {team1_total_hp} | Joueur 2: {team2_total_hp}")
        self.show_result_popup(winner, team1_total_hp, team2_total_hp)


if __name__ == "__main__":
    root = tk.Tk()
    app = PokemonBattleGUI(root)
    root.mainloop()
