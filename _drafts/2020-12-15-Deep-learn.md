---
author: Philip Zucker
date: 2020-02-05 13:52:20+00:00
layout: post
title: Deep Learning
---

<script src="https://cdn.jsdelivr.net/npm/@tensorflow/tfjs@2.0.0/dist/tf.min.js"></script>
<script>
    console.log(tf.getBackend());
// Create a rank-2 tensor (matrix) matrix tensor from a multidimensional array.
const a = tf.tensor([[1, 2], [3, 4]]);
console.log('shape:', a.shape);
a.print();

// Or you can create a tensor from a flat array and specify a shape.
const shape = [2, 2];
const b = tf.tensor([1, 2, 3, 4], shape);
console.log('shape:', b.shape);
b.print();
const b = a.reshape([4, 1]);

 // Returns the multi dimensional array of values.
 a.array().then(array => console.log(array));
 // Returns the flattened data that backs the tensor.
 a.data().then(data => console.log(data));

const a = tf.tensor([[1, 2], [3, 4]]);
const y = tf.tidy(() => {
  const result = a.square().log().neg();
  return result;
});

</script>


https://teachablemachine.withgoogle.com/train - prwetty slick - upload training images easily
https://learn.ml5js.org/

https://codelabs.developers.google.com/?cat=tensorflow

How do you get good at deep learning?
How do you even know you're on the right track?




Tips:
Try to overfit. Sometimes I see people suggest try to overfit and then regularize
Overfitting = doing well on training and doing poorly on test

Try to give it a little longer
Normalize and zero mean inputs?
Fiddling with hyper parameters
Get your iterations fast. You're gonna be trying lots of bullshit
Try to simplify your problem - A general problem solving tactic
Ng had some good tips


Dropout ~ bagging. Interesting
data augmentation. Adding adversarial examples.


attention - transformer netowrk
proof search - sorin lerner Lerin, openai guy
http://cseweb.ucsd.edu/~lerner/papers/proverbot-mapl2020.pdf 
autoencoder

boltzmann machines?
deep learned GC. what was up with that

Resources:

https://atcold.github.io/pytorch-Deep-Learning/ Yann Lecun's course

https://developers.google.com/machine-learning/crash-course google crash course

https://www.deeplearningbook.org/

https://www.tensorflow.org/tutorials

Spectral graph NN. Take laplace eigenfunctions.

https://bair.berkeley.edu/blog/ Berkely blog
http://rail.eecs.berkeley.edu/index.html - sergei levine group
https://ai.googleblog.com/



fast.ai

Path Kernels https://news.ycombinator.com/item?id=25314830 integrate gradient dot products over training path as similarity measure