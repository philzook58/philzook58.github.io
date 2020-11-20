---
author: philzook58
comments: true
date: 2017-07-20 15:10:19+00:00
layout: post
link: https://www.philipzucker.com/blockchain/
slug: blockchain
title: Blockchain
wordpress_id: 774
---

https://www.youtube.com/watch?v=bBC-nXj3Ng4



This is a great video.

To summarize:

Digital signatures are a way to verify that you wrote a message. Ordinarily I of the public private key communication as giving out the public key so that people can encode messages that I decrypt with the private key. This is the opposite. I lock up the message with the private key and people can unlock/verify it with the public key. It is difficult for people to find a way to lock up a message that will decrypt with that same public key.

Cryptographic Hash functions make a summary of a small number of bits that is difficult to find a message that makes the same summary hash.

Your bitcoin address is the public key. I think you have a wallet that can manage multiple public/private pairs. Possibly transferring money between them.

Bitcoin has the miners append a number to the end of the transaction list trying to find a hash that has a long string of zeros. Since you're just basically randomly trying numbers anyway, it doesn't hurt you to add in more transactions as they come in I think.

The blocks form kind of a funky linked list, where instead of a pointer you have the hash of the previous block. People trust the longest chain they can find, which was really hard to compute.

Miners can be incentivized to include transactions into their block. In general it seems like the protocol is a bit extendable by the consensus of the community. You can sort of vote on changes to the protocol by including your vote in the the hashed block.
