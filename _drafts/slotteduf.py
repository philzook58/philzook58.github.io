from dataclasses import dataclass, field


@dataclass(frozen=True)
class Slot:
    name: int

    def __repr__(self):
        return f"${self.name}"


counter = 0


def fresh_slot():
    global counter
    counter += 1
    return Slot(counter)


fresh_slot()

from typing import Optional


@dataclass(frozen=True)
class Renaming:
    map: list[tuple[Slot, Slot]]

    def rev(self):
        return Renaming([(b, a) for (a, b) in self.map])

    def keys(self):
        return [a for (a, b) in self.map]

    def values(self):
        return [b for (a, b) in self.map]

    def get(self, key: Slot):
        for a, b in self.map:
            if a == key:
                return b
        return key

    def __getitem__(self, key: Slot):
        for a, b in self.map:
            print((a, b, key))
            if a == key:
                return b
        raise KeyError(key)

    def compose(p, q):
        return Renaming([(a, q[b]) for (a, b) in p])


type Id = int


@dataclass(frozen=True)
class RenamedId:
    # gid : AppliedEId
    id: Id
    renaming: Renaming

    def __repr__(self):
        return f"{self.id} @ {self.renaming}"


@dataclass
class SlottedUF:
    uf: list[RenamedId] = field(default_factory=list)
    public_slots: dict[Id, set[Slot]] = field(default_factory=dict)
    # uf table is conceptually identity function. Yeaaaa?
    # uf : list[tuple[Renaming, Id]]

    def makeset(
        self, slots: list[Slot]
    ) -> RenamedId:  # it will be an identity tranformation
        n = len(self.uf)
        eid = RenamedId(n, Renaming([(a, a) for a in slots]))
        self.uf.append(eid)
        return eid

    def find(self, ma: RenamedId) -> RenamedId:
        rename = ma.renaming
        a = ma.id
        while True:
            mb = self.uf[a]
            print(rename)
            rename = mb.renaming.compose(rename)
            print(rename)
            if mb.id == a:
                return RenamedId(id=a, rename=rename)
            a = mb.id

    def union(self, a: RenamedId, b: RenamedId) -> bool:
        # redundant slots
        a, b = self.find(a), self.find(b)
        print(a, b)
        if a.id != b.id:
            self.uf[a.id] = RenamedId(b.id, b.renaming.compose(a.renaming.rev()))
            return True
        else:
            # symmettries
            return False

    def is_eq(self, a: RenamedId, b: RenamedId) -> bool:
        a = self.find(a)
        b = self.find(b)
        # but actually symmettries
        return a.id == b.id and all(
            a.renaming.get(s) == b.renaming.get(s) for s in a.renaming.keys()
        )


uf = SlottedUF()
slots = [fresh_slot() for _ in range(2)]
x, y, z = [uf.makeset(slots) for _ in range(3)]

x, y, z

uf.union(x, y)
