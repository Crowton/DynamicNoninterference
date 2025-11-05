# Dynamic Non-interference of Simple Small-step Language

This project builds on [https://github.com/aslanix/SmallStepNI/](https://github.com/aslanix/SmallStepNI/) by Aslan Askarov.

The proof covers a simple small-step language and shows that it adheres the non-interference property. In the original proof by Askarov, this is achieved by a type-checking system. In this new proof, it is instead achieved by a dynamic check at execution time.

The proof follows the bridge argument of Askarov, with a slight difference.
For more details on the semantics and proof structure, see [Dynamic_Noninterference.pdf](Dynamic_Noninterference.pdf), and alternatively the project of Askarov.
