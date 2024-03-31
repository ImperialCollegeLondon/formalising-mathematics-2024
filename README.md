# Formalising Mathematics

This is the repository for Kevin Buzzard's 2024 course on formalising mathematics in the Lean theorem prover. The course ran from January to March 2024. 

Note: this course is written in Lean 4. Previous versions of this course were written in the (now end-of-life) Lean 3.

## Local installation

First you need to install Visual Studio Code and the Lean 4 extension. Instructions for doing that are [here](https://leanprover-community.github.io/get_started.html#regular-install).

Then it's just a matter of installing this repository onto your computer. There are two ways to do this.

### Local installation via point-and-click

The most painless way to install the repository is using VS Code directly. With Lean installed, open any file on your system in VS Code, and then click on the upside-down A

![an upside-down A](png/clone_forall.png?raw=true "an upside-down A")

and select `Open Project` -> `Project: Download Project`. Type in the following URL into the text box which appeared:

```
https://github.com/ImperialCollegeLondon/formalising-mathematics-2024
```

and then select the directory where you want the project installed, type in the name of a folder (for example formalising-mathematics-2024) and then wait for a minute or two while everything downloads and compiles. Then accept the suggestion to open the course directory, and you should be up and running. Open up VS Code's file explorer (it looks like this)

![File explorer](png/file_explorer.png?raw=true "File explorer")

and navigate to the `FormalisingMathematics2024` directory, where you should find a whole bunch of directories containing the exercises.

### Local installation via command line

An older way is via the command line. Fire up the same command line which you used to install Lean 4 and type this:

```bash
git clone git@github.com:ImperialCollegeLondon/formalising-mathematics-2024.git
cd formalising-mathematics-2024
lake exe cache get
```

Now open the folder `formalising-mathematics-2024` which you just created, using VS Code's "open folder" functionality. You will find all the exercises for the course inside a subdirectory called `FormalisingMathematics2024` (don't confuse these two
directories! One has hyphens, the other does not).
## Online play

If you don't have the 4.5 gigabytes necessary to install all this, or if your computer is too slow to make the experience of using Lean on it fun (you'll need at least 8 gigs of ram, for example), then you can do the course exercises through a web browser (and you don't need to install anything onto your computer using this method).

### Method 1: via Gitpod.

Just click here: [![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/ImperialCollegeLondon/formalising-mathematics-2024)



### Method 2: via Codespaces

Go to the project's [home page on GitHub](https://github.com/ImperialCollegeLondon/formalising-mathematics-2024),
click "Code" and then "Codespaces" so it looks like this:

Pic: ![codespaces installation](png/codespaces.png?raw=true "codespaces installation")

Then click on the `+` ("create codespace on main"), and then wait for a few minutes. When it looks like everything has downloaded, open up the `FormalisingMathematics2024` directory (not the file!) and you should see the directories where the exercises are.

## Course notes

They are [here](https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/). 
