# Coin

An interesting question about finite communicative groups and group isomorphisms.

## Introduction

Let $G=(0,+)$ be a finite communicative group, and $f$ be any group isomorphism on $G$. We define a two-player game between an attacker (Alice) and a defender (David):

1. David chooses an element $x_0\in G$ without letting Alice know.
2. The $i$-th attack-defense procedure computes $x_i$ from $x_{i-1}$:
   1. If $x_{i-1}=0$, the game is over and Alice the attacker wins.
   2. Alice chooses an element $a_{i-1}\in G$, and tells David.
   3. David chooses a natural number $d_{i-1}\in\mathbb{N}$ accordingly, and computes $x_i=f^{d_{i-1}}(x_{i-1})+a_{i-1}$. Again, Alice has no idea what $d_{i-1}$ and $x_i$ are.
3. If the game still hasn't been over after $|G|-1$ attack-defense procedures, and $x_{|G|-1}\ne0$, then David the defender wins.

The game is deterministic, so there must be a definite winner. This project aims to answer the following question:

    Under what conditions can Alice the attacker win the game?

We give three different conditions equivalent to Alice's victory. In the last section, we give a concrete example regarding coins on a circle ring.

## File Structure

![structure](img/coin.svg)
