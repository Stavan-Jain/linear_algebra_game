import Game.Levels.DemoWorld
import Game.Lib.Tuple.Basic
import Game.Lib.Tuple.Functor
import Game.Lib.Tuple.GetElem

-- Here's what we'll put on the title screen
Title "The Linear Algebra Game"
Introduction
"
Welcome to the linear algebra game! It works as a learning tool for Duke University’s introductory
linear algebra course “Math 221: Linear Algebra and Applications.”

It also serves to introduce you to Lean: a proof assistant that provides an environment and language
to encode proofs formally.

The linear algebra game is intended to supplement your studies in 221. While in class you will learn
to write traditional proofs (in natural language), the game will

show you how to approach such proofs formally. A formal proof is written in precise syntax and can
be checked algorithmically by a computer program called a proof assistant.
"

Info "
Developed by: Yannan Bai, Annapurna Bhattacharya, Stavan Jain, Kurt Ma, Ricardo Prado Cunha,
Anoushka Sinha.

This game was originally developed as a part of Duke University's Math+ summer program.
"

/-! Information to be displayed on the servers landing page. -/
Languages "English"
CaptionShort "Undergraduate-level linear algebra in Lean"
CaptionLong "TODO"
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
