import React from 'react'
import RGivenList from '../containers/RGivenList'
import RAddGiven from '../containers/RAddGiven'

const GivenBlock = () => (
  <div>
    <h2>Givens</h2>
    <RGivenList />
    <RAddGiven />
  </div>
)

export default GivenBlock

