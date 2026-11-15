---
layout: post
title:  "Computer Systems: A Computation Theorist's Perspective"
---
I took [CMU 15-213 Computer Systems: A Programmer's Perspective](https://csapp.cs.cmu.edu/) when I was in college. The course teaches some useful stuff like using GDB and how cache works, but I found myself memorizing many details of the systems like the layout of the page table without understanding the big picture, and I barely remember anything about the course now.

Recently I'm taking the course [MIT 18.404J - Theory of Computation](https://ocw.mit.edu/courses/18-404j-theory-of-computation-fall-2020/), and realized that
- Abstract computation models like Turing machine can be used to explain computer systems in a way that is both rigorous and intuitive.
- Examples in the real world helps us to better understand the abstract models.

In this post, I'm going to provide some insights about how computer systems work using ideas from the theory of computation.

## Turing Machines

Let's start with the definitions.

**Definition.**\label{def:turing-machine} A (deterministic) *Turing machine* contains:
- A set of *states* \(Q\),
- A set of characters \(\Gamma\) that serves as *tape alphabet*,
- A function \(\delta:Q\times\Gamma\to Q\times\Gamma\times\{L,R\}\) called *transition function*, and
- Three special states \(q_0,q_{accept},q_{reject}\in Q\) such that \(q_{reject}\neq q_{accept}\).

A *configuration* of a Turing machine contains:
- A state \(q\in Q\),
- A tape \(t_1t_2\dots\) where \(t_i\in\Gamma\), and
- An number \(p\in\mathbb{N}\) that indicates where the head is.

Turing machines run in the following fashion:
- A Turing machine starts with the configuration whose state is \(q_0\) and its \(p=1\). The tape is a finite string \(w\) (called *input*) followed by a string of a special empty symbol in \(\Gamma\).
- For a configuration \(C=(q,t_1t_2\dots,p)\), if \(\delta(q,t_p)=(q',t_p',L)\), then it *yields* the configuration \((q',t_1t_2\dots t_{p-1}t_p't_{p+1}\dots,\max(1,p-1))\).
- If \(\delta(q,t_p)=(q',t_p',R)\), then \(C\) yields \((q',t_1t_2\dots t_{p-1}t_p't_{p+1}\dots,p+1)\).
- A Turing machine *stops* at a configuration if its state is \(q_{accept}\) or \(q_{reject}\). The configuration yields nothing if it's in these states.

A Turing machine *accepts the input* \(w\) if there is a list of configurations \(C_1C_2\cdots C_n\) such that \(C_1\) is the starting configuration with input \(w\), \(C_i\) yields \(C_{i+1}\) and \(C_n\) contains \(q_{accept}\). \(\Box\)

The definition of Turing machine is tedious and messy, but when compared to other models that have similar capability, it's relatively easy to implement (compared to lambda calculus) and relatively easy to program (compared to Conway's game of life), so most computers today (with [Von Neumann architecture](https://en.wikipedia.org/wiki/Von_Neumann_architecture)) are modeled after Turing machine:
- \(Q\) is represented by the values of registers and CPU flags.
- The tape \(\Gamma^*\) is represented by the memory.
- \(\delta\) is simplified to a set of instructions.
- The tape position in the configuration can be seen as the program counter or other registers that can be used to index memory.
- Users may want to connect their computer to *peripheral devices* like a disk driver or monitor. There are two popular ways to do so:
  - Port-mapped I/O: extending the state \(Q\) by adding device states. These states can be accessed by instructions like `in` and `out` in x86.
  - Memory-mapped I/O: mark an area of the tape as the interface to the device. The Turing machine interacts to the device by reading/writing the tape.

There are some subtle differences like the memory can be random-accessed with multiple heads and the instructions also lives in the memory. You can still prove that machines with these properties are still equivalent to some Turing machines. [^infinite]

[^infinite]: Here's a real gap between TM and real-world machines: TM has a infinite tape and no machine have infinite memory. We can address this issue by assuming that we always have more memory than the problem requires.

## Time-sharing and Nondeterminism

In 1960s, computers are getting fast enough to run [time-sharing systems](https://en.wikipedia.org/wiki/Time-sharing). These systems may still be run on a Turing machine, but the computation model they provide to the users are different.

Take [Unix](https://en.wikipedia.org/wiki/Unix) for an example. A Unix system can have many processes, each of them looks as if they are running on its own CPU and has its own memory space, and you can `fork()` a process to create two processes. The Unix user space can not be modeled precisely as a deterministic Turing machine, therefore we need a more capable model from theory of computation:

**Definition.**\label{def:nondet-turing-machine} A *nondeterministic Turing machine* (NTM) is the same as a Turing machine, except that
- \(\delta:Q\times\Gamma\to\mathcal{P}(Q\times\Gamma\times\{L,R\})\).
- A configuration becomes a set of tuples \(\{(q_i,t_1^{(i)}t_2^{(i)}\dots,p_i)\}\). \(C\) yields \(C'\) if \(C'=\bigcup_{c\in C}\delta(c)\) where \(\delta(c)\) means using \(\delta\) to update \(c\) in a way similar to deterministic Turing machines.
- A nondeterministic Turing machine stops when at least one state in the configuration is \(q_{accept}\) or all of the states are \(q_{reject}\). The input is accepted if there is a \(q_{accept}\). \(\Box\)

So the Unix user space is a nondeterministic Turing machine:
- A process is a tuple in the configuration,
- Most of the time \(\delta\) returns a singleton set, and when the configuration corresponds to `fork()`, \(\delta\) returns a set with two tuples that are identical except the return value of `fork()`.
- Unix have some mechanism for process to communicate with each other like *pipes*. We choose to ignore the fact for simplicity and assumes that processes are running in complete isolation.
- There is a process called the *shell* that are designed to loop forever and run your programs instead of returning \(q_{accept}\) or \(q_{reject}\).

A Unix system can be running on a single-core CPU, which is a deterministic Turing machine. How can the Unix developers build a more capable model based on a less capable once? Because they are the same from computation theorists' point of view.

**Proposition.**\label{prop:nondeterminism-equivalent} For a nondeterministic Turing machine \(N=(Q,\Gamma,\delta,q_0,q_{accept},q_{reject})\), we can build a deterministic Turing machine \(D\) that is equivalent to \(N\), i.e. \(N\) accepts input \(w\) iff \(D\) accepts input \(w\). [^other]

[^other]: We only prove the accepting case here. The equivalence of other cases like looping forever (which may be useful when you are building the shell) are similar.

*proof.* I'll present the machine without explain anything and give a interpretation later.

Assume that
- We have some ways to represent numbers on a tape. We can't directly add \(\mathbb{N}\) to the alphabet because the alphabet must be finite, but we can use some representation like \(R=\{0,1,\dots,9\}\) and combine them. I'll directly write numbers on the tape for simplicity.
- \(Q,\Gamma,\{\#\},R\) are disjoint. If \(x\) is in both \(Q\) and \(\Gamma\), you can replace them with different symbols like \(x_Q,x_\Gamma\).

Let the tape alphabet of \(D\) be \(\Gamma\cup Q\cup\{\#\}\cup R\). I'll describe \(D\) in pseudocode and everyone with enough background knowledge and time can write down other parts of \(D\).

Assume that the input is \(w_1,w_2,\dots,w_n\). The first thing \(D\) does is to rewrite the tape as
\[1,1,q_0,1,w_1,w_2,\dots,w_n,\#.\]

Then it goes into a loop:
1. \(x\gets T_2\), where \(T\) is the tape and \(T_i\) is the value of the \(i\)-th (started from 1) cell of \(T\).
2. Move the head to the right until the head met \(x\) symbols from \(Q\). Now the head is pointing to a symbol in \(Q\).
3. \(q\gets\) the head's value, and \(p\gets\) the value of the cell on the right.
4. Move the head to the right again until it met another symbol in \(Q\) or \(\#\). Remember the symbols in between as \(t_1,t_2,\dots,t_m\).
5. If \(p>m\), let \(t_{m+1},\dots,t_p\) be the blank character and \(u=p\), otherwise \(u=m\).
6. \(\{(q_1,t_1^{(1)}\dots t_u^{(1)},p_1),\dots,(q_v,t_1^{(v)}\dots t_u^{(v)},p_v)\}\gets\delta(q,t_1t_2\dots t_u)\).
7. If one of the \(q_1,\dots,q_v\) is \(q_{accept}\), then \(D\) halts with \(q_{accept}\).
8. Filter out the tuples with \(q_{reject}\). Suppose that now there are \(v'\) tuples in the set.
9. Move the head to the position in step 4, then for every cell \(T_j\) behind the head (i.e. with a index greater or equal to the head's position), move it to \(T_{j+v'(u+2)-(m+2)}\).
10. If \(v'>0\), step 9 creates a space of \(v'(u+2)-(m+2)\) cells. fill the space with
    \[q_1,p'_1,t_1^{(1)},\dots,t_1^{(u)},\dots,q_{v'},p'_v,t_1^{(v')},\dots,t_1^{(v')},\]

    where
    \[
    p'_i=\begin{cases}
        \max(1, p-1), & p_i=L, \\
        p+1, & p_i=R.
    \end{cases}\]
11. \(T_1\gets T_1+v'-1\). If \(T_1=0\), halts with \(q_{reject}\), otherwise \(T_2\gets(T_2+1)\ \mathrm{mod}\ T_1\).
12. Go to step 1.

\(N\) accepts the input iff there is a set of configuration \(C_1,C_2,\dots,C_\tau\) such that \(C_i\) yields \(C_{i+1}\). We need to prove that this is equivalent to "\(D\) accepts the input".

Because we are using the same \(\delta\), therefore \(C_i\) yields \(C_{i+1}\) iff the assignments that corresponds to this yield in step 6 of the code of \(D\), then \(C_\tau\) contains \(q_{accept}\) iff we enter step 7 iff \(D\) accepts the input. \(\Box\)

## An Operating System

Here's an interpretation of the proof \ref{prop:nondeterminism-equivalent}: the Turing machine \(D\) is an *operating system kernel* whose user interface is the nondeterministic Turing machine \(N\). In our question about Unix user space, let \(N\) be the Unix's user space, then the Turing machine \(D\) can be the actual implementation of Unix kernel on a single-core CPU.

If you are familiar with operating systems, you may have noticed that \(D\) contains some of the key features of OSes:
- Address space: the kernel sees the entire address space and does some bookkeeping to maintain the illusion that each process has its own address space. In my proof, I'm using the simplest approach which may leads to lots of copying. Modern OSes usually implement mechanism like *paging* and *copy-on-write* to reduce copying.
- Scheduling: the kernel uses a technique called round-robin to choose a process to simulate after the previous process yields. There are better ways to chooses which process to execute, so processes like GUI programs won't hang for a long time.

There are also many things not covered by the simple implementation in the proof:
- Kernel trap: \(D\) simulates the entire user process in step 6, which may be costly. In real world scenario, the kernel and the user processes are usually written in the same instruction set architecture, so the user process can be run on the CPU directly until it requires the kernel's help (e.g. it fires up a system call) and "be trapped" into kernel.
- Page table: whenever a process reads or writes memory, \(D\) will translate the address into the actual memory address. If we have implemented kernel trap, then every memory read/write requires trapping into the kernel. Modern hardware uses page table to automatically translate user address to real address when reading/writing memory to avoid kernel traps. Page tables can also be used to catch the error when accessing memory or to protect parts of the memory from reading/writing.
- Privilege mode: malicious users may want to execute the instruction to change its page table and read the memory it shouldn't read. To avoid this, the hardware provides different privilege modes to distinguish the kernel from other processes and things like changing page tables can only be done by the kernel.

The list goes on and on as we are moving down the abstract layer. Computation Theorist won't be bothered by these nitty-gritty details, so we'd better stop here.

## Closing Thoughts

Computer system is hard even when the principle is simple, because "the principle" may abstract too much away from the real world. It's totally valid to claim that an OS is just a transformation from a nondeterministic Turing machine to a deterministic one, but knowing that is not sufficient to write an efficient and secure OS on a real hardware. The right abstraction helps us understand things, but to really understand and gain the skill of system programming, we need to go down the abstraction and get our hands dirty on big projects.

Here are some projects I have finished and would like to recommend if you are interested in OSes:
- [NJU ICS programming assignments](https://nju-projectn.github.io/ics-pa-gitbook/): write an emulator for the ISA of your choice, write a small OS that runs on your emulator, and port some games to your OS. Today's post borrowed some ideas from the instruction materials.
- [MIT 6.1810 Operating System Engineering](https://pdos.csail.mit.edu/6.1810/2026/): learn the source code and hack [xv6](https://github.com/mit-pdos/xv6-riscv), a small OS kernel inspired by Unix V6 and runs on RISC-V.

