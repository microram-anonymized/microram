// PageStore: the page-upload interface the version services use, extending the
// PageReader read interface (traversal.hpp) of the private proof batches.

#pragma once

#include "traversal.hpp"

namespace ethereum_mpt {

// Public update traffic only, serialized with complete private proof batches.
// Appended pages are immutable. Capacities include each enabled tier's dummy
// page; disabled tiers have capacity zero. Publication requires an explicit
// finish_pending_work() after all tier uploads have completed successfully.
class PageStore : public PageReader {
 public:
    virtual void write_pages_batch(Tier tier, std::uint64_t first_page_id,
                                  const std::vector<Page>& pages) = 0;
    virtual void finish_pending_work() = 0;
    virtual std::array<std::size_t, 3> capacities() const = 0;
};

}  // namespace ethereum_mpt
