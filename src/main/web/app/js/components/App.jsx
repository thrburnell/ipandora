import React from 'react'
import RGivensList from '../containers/RGivensList'
import RToShowList from '../containers/RToShowList'
import RAddGiven from '../containers/RAddGiven'
import RAddToShow from '../containers/RAddToShow'

const App = () => (
  <div>
    <RGivensList heading="Givens" />
    <RAddGiven />
    <RToShowList heading="To Show" />
    <RAddToShow />
  </div>
)

export default App

