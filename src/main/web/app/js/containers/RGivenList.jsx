import { connect } from 'react-redux'
import FormulaList from '../components/FormulaList'

const mapStateToProps = (state) => (
  {
    formulas: state.givens.map(key => state.knownFormulas[key])
  }
)

const RGivenList = connect(
  mapStateToProps
)(FormulaList)

export default RGivenList

