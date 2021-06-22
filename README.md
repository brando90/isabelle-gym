# Isabelle-Gym: a Reinforcement learning Environment and data set for Machine Learning for Theorem Proving

## TODO

The main help we need is finding a collaborator to help us create a data set for Isabelle. See issue:

https://github.com/brando90/isabelle-gym/issues/30

for details.

## Opening Isabelle Console

### On Mac

1. Go to the applications folder and then find the `isabelle` app
2. Right click and click on `show package contents`
3. Then click on soft link to folder `isabelle`
4. Go to the `bin` folder (or open the `bin` folder with the terminal)
5. open the `isabelle` executable by double clicking it or `./isabelle`

## Running Our Gym Prototype

Please refer to the `demo.ipynb` for how to use the gym. Make sure you set up your paths correctly.

### Setting Up PATH

For now, please add the isabelle binary to your paths, by:

1. Find out what the directory of your desired `isabelle` binary is (the instruction above is helpful for Mac users)
#### On mac
- option 1: paths are stored in `/etc/paths`, add the directory to your `/etc/paths`, you will need sudo permission for this
- option 2: you can also edit your paths using bash/zsh profiles, by: https://hathaway.cc/2008/06/how-to-edit-your-path-environment-variables-on-mac/
#### On Linux
- there are many options, chose the method you prefer: https://stackoverflow.com/questions/37676849/where-is-path-variable-set-in-ubuntu

Esentially, you want to be able to call `isabelle console` (or `isabelle` whatever) in your terminal under any directory. 

## Discussion and question

Consider opening a discussion post before an issue if your post is more of a question or discussion about new features: https://github.com/brando90/isabelle-gym/discussions


## Citation

If you find our code useful consider citing us:
```
@software{isagym2021,
    author={Jize Jiang, Qikai Yang, Alan Andrade, Dun Ma, Brando Miranda},
    title={isabelle-gym},
    url={https://github.com/brando90/isabelle-gym},
    year={2021}
}
```
