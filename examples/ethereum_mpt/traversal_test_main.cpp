// Entry point running the fixed-helper, fixed-parser and traversal suites.

#include <exception>
#include <iostream>

void run_fixed_tests();
void run_fixed_node_tests();
void run_traversal_tests();

int main() {
    try {
        run_fixed_tests();
        run_fixed_node_tests();
        run_traversal_tests();
        std::cout << "ethereum_mpt_traversal_test passed\n";
    } catch (const std::exception& error) {
        std::cerr << "ethereum_mpt_traversal_test: " << error.what() << '\n';
        return 1;
    }
}
